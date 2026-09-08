/-
Copyright (c) 2021 Alex Kontorovich and Heather Macbeth and Marc Masdeu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth, Marc Masdeu
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Instances.ZMultiples
public import Mathlib.Topology.OpenPartialHomeomorph.Continuity

/-!
# The action of the modular group SL(2, ℤ) on the upper half-plane

We define the action of `SL(2,ℤ)` on `ℍ` (via restriction of the `SL(2,ℝ)` action in
`Analysis.Complex.UpperHalfPlane`). We then define the standard fundamental domain
(`ModularGroup.fd`, `𝒟`) for this action and show (`ModularGroup.exists_smul_mem_fd`)
that any point in `ℍ` can be moved inside `𝒟`.

## Main definitions

The standard (closed) fundamental domain of the action of `SL(2,ℤ)` on `ℍ`, denoted `𝒟`:
`fd := {z | 1 ≤ (z : ℂ).normSq ∧ |z.re| ≤ (1 : ℝ) / 2}`

The standard open fundamental domain of the action of `SL(2,ℤ)` on `ℍ`, denoted `𝒟ᵒ`:
`fdo := {z | 1 < (z : ℂ).normSq ∧ |z.re| < (1 : ℝ) / 2}`

These notations are localized in the `Modular` scope and can be enabled via `open scoped Modular`.

## Main results

* `ModularGroup.exists_smul_mem_fd`: Any `z : ℍ` can be moved to `𝒟` by an element of `SL(2,ℤ)`.
* `ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fd`:
  The open fundamental domain `𝒟ᵒ` is disjoint from `g • 𝒟` for any `g ≠ ±1`.
* `ModularGroup.eq_smul_self_of_mem_fdo_mem_fdo`:
  If both `z` and `γ • z` are in the open domain `𝒟ᵒ` then `z = γ • z`.
* `ModularGroup.fdo_eq_interior_fd` and `ModularGroup.fd_eq_closure_fdo`: topological relations
  between `fd` and `fdo`.

## Discussion

Standard proofs make use of the identity

`g • z = a / c - 1 / (c (cz + d))`

for `g = [[a, b], [c, d]]` in `SL(2)`, but this requires separate handling of whether `c = 0`.
Instead, our proof makes use of the following perhaps novel identity (see
`ModularGroup.smul_eq_lcRow0_add`):

`g • z = (a c + b d) / (c^2 + d^2) + (d z - c) / ((c^2 + d^2) (c z + d))`

where there is no issue of division by zero.

Another feature is that we delay until the very end the consideration of special matrices
`T=[[1,1],[0,1]]` (see `ModularGroup.T`) and `S=[[0,-1],[1,0]]` (see `ModularGroup.S`), by
instead using abstract theory on the properness of certain maps (phrased in terms of the filters
`Filter.cocompact`, `Filter.cofinite`, etc) to deduce existence theorems, first to prove the
existence of `g` maximizing `(g•z).im` (see `ModularGroup.exists_max_im`), and then among
those, to minimize `|(g•z).re|` (see `ModularGroup.exists_row_one_eq_and_min_re`).

The characterization of cases with `z ∈ 𝒟` and `g • z ∈ 𝒟` follows Theorem VII.1 [serre1973].
-/

@[expose] public section

open Complex hiding I

open Matrix hiding mul_smul

open Matrix.SpecialLinearGroup UpperHalfPlane ModularGroup Topology

noncomputable section

open scoped ComplexConjugate MatrixGroups

namespace ModularGroup

variable {g : SL(2, ℤ)} (z : ℍ)

section BottomRow

/-- The two numbers `c`, `d` in the "bottom row" of `g=[[*,*],[c,d]]` in `SL(2, ℤ)` are coprime. -/
/-
**ModularGroup.bottom_row_coprime** 是 Mathlib 中的一个定理，位于命名空间 `ModularGroup`。
形式化陈述：bottom_row_coprime {R : Type*} [CommRing R] (g : SL(2, R)) : IsCoprime ((↑
g : Matrix (Fin 2) (Fin 2) R) 1 0) ((↑g : Matrix (Fin 2) (Fin 2) R) 1 1)
参数：g : SL(2, R)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matrix.SpecialLinearGroup.isCoprime_row`：isCoprime_row (A : SL(2, R)) (i
 : Fin 2) : IsCoprime (A i 0) (A i 1)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)

--- 原说明 ---
The two numbers `c`, `d` in the "bottom row" of `g=[[*,*],[c,d]]` in `SL(2, ℤ)` 
are coprime.
-/
theorem bottom_row_coprime {R : Type*} [CommRing R] (g : SL(2, R)) :
    IsCoprime ((↑g : Matrix (Fin 2) (Fin 2) R) 1 0) ((↑g : Matrix (Fin 2) (Fin 2) R) 1 1) :=
  isCoprime_row g 1

/-- Every pair `![c, d]` of coprime integers is the "bottom row" of some element `g=[[*,*],[c,d]]`
of `SL(2,ℤ)`. -/
/-
**ModularGroup.bottom_row_surj** 是 Mathlib 中的一个定理，位于命名空间 `ModularGroup`。
形式化陈述：bottom_row_surj {R : Type*} [CommRing R] : Set.SurjOn (fun g : SL(2, R) =>
 (↑g : Matrix (Fin 2) (Fin 2) R) 1) Set.univ {cd | IsCoprime (cd 0) (cd 1)}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det_fin_two`：det_fin_two (A : Matrix (Fin 2) (Fin 2) R) : det A =
 A 0 0 * A 1 1 - A 0 1 * A 1 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
Every pair `![c, d]` of coprime integers is the "bottom row" of some element `g=
[[*,*],[c,d]]`
of `SL(2,ℤ)`.
-/
theorem bottom_row_surj {R : Type*} [CommRing R] :
    Set.SurjOn (fun g : SL(2, R) => (↑g : Matrix (Fin 2) (Fin 2) R) 1) Set.univ
      {cd | IsCoprime (cd 0) (cd 1)} := by
  rintro cd ⟨b₀, a, gcd_eqn⟩
  let A := of ![![a, -b₀], cd]
  have det_A_1 : det A = 1 := by
    convert! gcd_eqn
    rw [det_fin_two]
    simp [A, (by ring : a * cd 1 + b₀ * cd 0 = b₀ * cd 0 + a * cd 1)]
  refine ⟨⟨A, det_A_1⟩, Set.mem_univ _, ?_⟩
  ext; simp [A]

end BottomRow

section TendstoLemmas

open Filter ContinuousLinearMap

attribute [local simp] FunLike.coe_smul

/-- The function `(c,d) → |cz+d|^2` is proper, that is, preimages of bounded-above sets are finite.
-/
/-
**ModularGroup.tendsto_normSq_coprime_pair** 是 Mathlib 中的一个定理，位于命名空间 `ModularGro
up`。
形式化陈述：tendsto_normSq_coprime_pair : Filter.Tendsto (fun p : Fin 2 -> Int => norm
Sq ((p 0 : Complex) * z + p 1)) cofinite atTop
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Complex.ofReal_intCast`：∀ (n : ℤ), ↑↑n = ↑n
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `UpperHalfPlane.coe_im_pos`：∀ (self : UpperHalfPlane), 0 < (↑self).im
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
· 使用定理 `LinearMap.smul_apply`：smul_apply (a : S) (f : M ->ₛₗ[σ₁₂] M₂) (x : M) : 
(a • f) x = a • f x
· 使用定理 `LinearMap.id_apply`：id_apply (x : M) : @id R M _ _ _ x = x
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `Complex.add_im`：add_im (z w : Complex) : (z + w).im = z.im + w.im
· 使用定理 `Complex.im_ofReal_mul`：im_ofReal_mul (r : Real) (z : Complex) : (r * z).
im = r * z.im
· 使用定理 `Complex.ofReal_im`：ofReal_im (r : Real) : (r : Complex).im = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `RingHomClass.toLinearMapClassNNRat`：∀ {F : Type u_1} {R : Type u_2} {S :
 Type u_3} [inst : DivisionSemiring R] [inst_1 : CharZero R]   [inst_2 : Divisio
nSemiring S] [inst_3 : C…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
（共 66 条，此处仅展示前 30 条）

--- 原说明 ---
The function `(c,d) → |cz+d|^2` is proper, that is, preimages of bounded-above s
ets are finite.
-/
theorem tendsto_normSq_coprime_pair :
    Filter.Tendsto (fun p : Fin 2 → ℤ => normSq ((p 0 : ℂ) * z + p 1)) cofinite atTop := by
  -- using this instance rather than the automatic `Function.module` makes unification issues in
  -- `LinearEquiv.isClosedEmbedding_of_injective` less bad later in the proof.
  let : Module ℝ (Fin 2 → ℝ) := NormedSpace.toModule
  let π₀ : (Fin 2 → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj 0
  let π₁ : (Fin 2 → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj 1
  let f : (Fin 2 → ℝ) →ₗ[ℝ] ℂ := π₀.smulRight (z : ℂ) + π₁.smulRight 1
  have f_def : ⇑f = fun p : Fin 2 → ℝ => (p 0 : ℂ) * ↑z + p 1 := by
    ext1
    dsimp only [π₀, π₁, f, LinearMap.coe_proj, real_smul, LinearMap.coe_smulRight,
      LinearMap.add_apply]
    rw [mul_one]
  have :
    (fun p : Fin 2 → ℤ => normSq ((p 0 : ℂ) * ↑z + ↑(p 1))) =
      normSq ∘ f ∘ fun p : Fin 2 → ℤ => ((↑) : ℤ → ℝ) ∘ p := by
    ext1
    rw [f_def]
    dsimp only [Function.comp_def]
    rw [ofReal_intCast, ofReal_intCast]
  rw [this]
  have hf : LinearMap.ker f = ⊥ := by
    let g : ℂ →ₗ[ℝ] Fin 2 → ℝ :=
      LinearMap.pi ![imLm, imLm.comp ((z : ℂ) • ((conjAe : ℂ →ₐ[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ))]
    suffices ((z : ℂ).im⁻¹ • g).comp f = LinearMap.id by exact LinearMap.ker_eq_bot_of_inverse this
    apply LinearMap.ext
    intro c
    have hz : (z : ℂ).im ≠ 0 := z.2.ne'
    rw [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply]
    ext i
    dsimp only [Pi.smul_apply, LinearMap.pi_apply, smul_eq_mul]
    fin_cases i
    · change (z : ℂ).im⁻¹ * (f c).im = c 0
      rw [f_def, add_im, im_ofReal_mul, ofReal_im, add_zero, mul_left_comm, inv_mul_cancel₀ hz,
        mul_one]
    · change (z : ℂ).im⁻¹ * ((z : ℂ) * conj (f c)).im = c 1
      rw [f_def, map_add, map_mul, mul_add, mul_left_comm, mul_conj, conj_ofReal,
        conj_ofReal, ← ofReal_mul, add_im, ofReal_im, zero_add, inv_mul_eq_iff_eq_mul₀ hz]
      simp only [ofReal_im, ofReal_re, mul_im, zero_add, mul_zero]
  have hf' : IsClosedEmbedding f := f.isClosedEmbedding_of_injective hf
  have h₂ : Tendsto (fun p : Fin 2 → ℤ => ((↑) : ℤ → ℝ) ∘ p) cofinite (cocompact _) := by
    convert! Tendsto.pi_map_coprodᵢ fun _ => Int.tendsto_coe_cofinite
    · rw [coprodᵢ_cofinite]
    · rw [coprodᵢ_cocompact]
  exact tendsto_normSq_cocompact_atTop.comp (hf'.tendsto_cocompact.comp h₂)

/-- Given `coprime_pair` `p=(c,d)`, the matrix `[[a,b],[*,*]]` is sent to `a*c+b*d`.
  This is the linear map version of this operation.
-/
/-
**ModularGroup.lcRow0** 是 Mathlib 中的一个定义，位于命名空间 `ModularGroup`。
形式化陈述：lcRow0 (p : Fin 2 -> Int) : Matrix (Fin 2) (Fin 2) Real ->ₗ[Real] Real
参数：p : Fin 2 -> Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `coprime_pair` `p=(c,d)`, the matrix `[[a,b],[*,*]]` is sent to `a*c+b*d`.
  This is the linear map version of this operation.
-/
def lcRow0 (p : Fin 2 → ℤ) : Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] ℝ :=
  ((p 0 : ℝ) • LinearMap.proj (0 : Fin 2) +
      (p 1 : ℝ) • LinearMap.proj (1 : Fin 2) : (Fin 2 → ℝ) →ₗ[ℝ] ℝ).comp
    (LinearMap.proj 0)

@[simp]
/-
**ModularGroup.lcRow0_apply** 是 Mathlib 中的一个定理，位于命名空间 `ModularGroup`。
形式化陈述：lcRow0_apply (p : Fin 2 -> Int) (g : Matrix (Fin 2) (Fin 2) Real) : lcRow0
 p g = p 0 * g 0 0 + p 1 * g 0 1
参数：p : Fin 2 -> Int；g : Matrix (Fin 2) (Fin 2) Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lcRow0_apply (p : Fin 2 → ℤ) (g : Matrix (Fin 2) (Fin 2) ℝ) :
    lcRow0 p g = p 0 * g 0 0 + p 1 * g 0 1 :=
  rfl

/-- Linear map sending the matrix [a, b; c, d] to the matrix [ac₀ + bd₀, - ad₀ + bc₀; c, d], for
some fixed `(c₀, d₀)`. -/
@[simps!]
/-
**ModularGroup.lcRow0Extend** 是 Mathlib 中的一个定义，位于命名空间 `ModularGroup`。
形式化陈述：lcRow0Extend {cd : Fin 2 -> Int} (hcd : IsCoprime (cd 0) (cd 1)) : Matrix 
(Fin 2) (Fin 2) Real ≃ₗ[Real] Matrix (Fin 2) (Fin 2) Real
参数：hcd : IsCoprime (cd 0) (cd 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Linear map sending the matrix [a, b; c, d] to the matrix [ac₀ + bd₀, - ad₀ + bc₀
; c, d], for
some fixed `(c₀, d₀)`.
-/
def lcRow0Extend {cd : Fin 2 → ℤ} (hcd : IsCoprime (cd 0) (cd 1)) :
    Matrix (Fin 2) (Fin 2) ℝ ≃ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
  LinearEquiv.piCongrRight
    ![by
      refine
        LinearMap.GeneralLinearGroup.generalLinearEquiv ℝ (Fin 2 → ℝ)
          (GeneralLinearGroup.toLin (planeConformalMatrix (cd 0 : ℝ) (-(cd 1 : ℝ)) ?_))
      norm_cast
      rw [neg_sq]
      exact hcd.sq_add_sq_ne_zero, LinearEquiv.refl ℝ (Fin 2 → ℝ)]

set_option backward.isDefEq.respectTransparency false in
/-- The map `lcRow0` is proper, that is, preimages of cocompact sets are finite in
`[[* , *], [c, d]]`. -/
/-
**ModularGroup.tendsto_lcRow0** 是 Mathlib 中的一个定理，位于命名空间 `ModularGroup`。
形式化陈述：tendsto_lcRow0 {cd : Fin 2 -> Int} (hcd : IsCoprime (cd 0) (cd 1)) : Tends
to (fun g : { g : SL(2, Int) // g 1 = cd } => lcRow0 cd ↑(↑g : SL(2, Real))) cof
inite (cocompact Real)
参数：hcd : IsCoprime (cd 0) (cd 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `continuous_matrix`：continuous_matrix [TopologicalSpace α] {f : α -> Matr
ix m n R} (h : forall i j, Continuous fun a => f a i j) : Continuous f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.Tendsto.of_tendsto_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Typ
e u_3} {f : α → β} {g : β → γ} {a : Filter α} {b : Filter β} {c : Filter γ},   F
ilter.Tendsto (g ∘ f…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.coprodᵢ_cofinite`：coprodᵢ_cofinite {α : ι -> Type*} [Finite ι] : 
(Filter.coprodᵢ fun i => (cofinite : Filter (α i))) = cofinite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Filter.coprodᵢ_cocompact`：Filter.coprodᵢ_cocompact {X : ι -> Type*} [for
all d, TopologicalSpace (X d)] : (Filter.coprodᵢ fun d => Filter.cocompact (X d)
) = Filter.coc…
· 使用定理 `Filter.Tendsto.pi_map_coprodᵢ`：∀ {ι : Type u_1} {α : ι → Type u_2} {f : 
(i : ι) → Filter (α i)} {β : ι → Type u_3} {m : (i : ι) → α i → β i}   {g : (i :
 ι) → Filter (β i)}…
· 使用定理 `Int.tendsto_coe_cofinite`：tendsto_coe_cofinite : Tendsto ((↑) : Int -> R
eal) cofinite (cocompact Real)
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Function.Injective.tendsto_cofinite`：Function.Injective.tendsto_cofinite
 {f : α -> β} (hf : Injective f) : Tendsto f cofinite cofinite
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `Homeomorph.isClosedEmbedding`：isClosedEmbedding (h : X ≃ₜ Y) : IsClosedE
mbedding h
· 使用定理 `instIsTopologicalAddGroupMatrix`：∀ {m : Type u_4} {n : Type u_5} {R : Ty
pe u_8} [inst : TopologicalSpace R] [inst_1 : AddGroup R]   [IsTopologicalAddGro
up R], IsTopologicalA…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `instContinuousSMulMatrix`：∀ {α : Type u_2} {m : Type u_4} {n : Type u_5}
 {R : Type u_8} [inst : TopologicalSpace R] [inst_1 : TopologicalSpace α]   [ins
t_2 : SMul α R…
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instT2SpaceMatrix`：∀ {m : Type u_4} {n : Type u_5} {R : Type u_8} [inst 
: TopologicalSpace R] [T2Space R], T2Space (Matrix m n R)
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
（共 84 条，此处仅展示前 30 条）

--- 原说明 ---
The map `lcRow0` is proper, that is, preimages of cocompact sets are finite in
`[[* , *], [c, d]]`.
-/
theorem tendsto_lcRow0 {cd : Fin 2 → ℤ} (hcd : IsCoprime (cd 0) (cd 1)) :
    Tendsto (fun g : { g : SL(2, ℤ) // g 1 = cd } => lcRow0 cd ↑(↑g : SL(2, ℝ))) cofinite
      (cocompact ℝ) := by
  let mB : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun t => of ![![t, (-(1 : ℤ) : ℝ)], (↑) ∘ cd]
  have hmB : Continuous mB := by
    refine continuous_matrix ?_
    simp only [mB, Fin.forall_fin_two, continuous_const, continuous_id', of_apply, cons_val_zero,
      cons_val_one, and_self_iff]
  refine Filter.Tendsto.of_tendsto_comp ?_ (comap_cocompact_le hmB)
  let f₁ : SL(2, ℤ) → Matrix (Fin 2) (Fin 2) ℝ := fun g =>
    Matrix.map (↑g : Matrix _ _ ℤ) ((↑) : ℤ → ℝ)
  have cocompact_ℝ_to_cofinite_ℤ_matrix :
    Tendsto (fun m : Matrix (Fin 2) (Fin 2) ℤ => Matrix.map m ((↑) : ℤ → ℝ)) cofinite
      (cocompact _) := by
    simpa only [coprodᵢ_cofinite, coprodᵢ_cocompact] using!
      Tendsto.pi_map_coprodᵢ fun _ : Fin 2 =>
        Tendsto.pi_map_coprodᵢ fun _ : Fin 2 => Int.tendsto_coe_cofinite
  have hf₁ : Tendsto f₁ cofinite (cocompact _) :=
    cocompact_ℝ_to_cofinite_ℤ_matrix.comp Subtype.coe_injective.tendsto_cofinite
  have hf₂ : IsClosedEmbedding (lcRow0Extend hcd) :=
    (lcRow0Extend hcd).toContinuousLinearEquiv.toHomeomorph.isClosedEmbedding
  convert! hf₂.tendsto_cocompact.comp (hf₁.comp Subtype.coe_injective.tendsto_cofinite) using 1
  ext ⟨g, rfl⟩ i j : 3
  fin_cases i <;> [fin_cases j; skip]
  -- the following are proved by `simp`, but it is replaced by `simp only` to avoid timeouts.
  · simp only [Fin.isValue, Int.cast_one, map_apply_coe, RingHom.mapMatrix_apply,
      Int.coe_castRingHom, lcRow0_apply, map_apply, Fin.zero_eta, Function.comp_apply,
      of_apply, cons_val', cons_val_zero, empty_val', cons_val_fin_one, lcRow0Extend_apply,
      LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv, GeneralLinearGroup.coe_toLin,
      val_planeConformalMatrix, neg_neg, mulVecLin_apply, mulVec, dotProduct, Fin.sum_univ_two,
      cons_val_one, mB, f₁]
  · convert! congr_arg (fun n : ℤ => (-n : ℝ)) g.det_coe.symm using 1
    simp only [Fin.zero_eta, Function.comp_apply, lcRow0Extend_apply, cons_val_zero,
      LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv, GeneralLinearGroup.coe_toLin,
      mulVecLin_apply, mulVec, dotProduct, det_fin_two, f₁]
    simp only [Fin.isValue, Fin.mk_one, val_planeConformalMatrix, neg_neg, of_apply, cons_val',
      empty_val', cons_val_fin_one, cons_val_one, map_apply, Fin.sum_univ_two,
      cons_val_zero, neg_mul, Int.cast_sub, Int.cast_mul, neg_sub]
    ring
  · rfl

/-- This replaces `(g•z).re = a/c + *` in the standard theory with the following novel identity:
  `g • z = (a c + b d) / (c^2 + d^2) + (d z - c) / ((c^2 + d^2) (c z + d))`
  which does not need to be decomposed depending on whether `c = 0`. -/
/-
**ModularGroup.smul_eq_lcRow0_add** 是 Mathlib 中的一个定理，位于命名空间 `ModularGroup`。
形式化陈述：smul_eq_lcRow0_add {p : Fin 2 -> Int} (hp : IsCoprime (p 0) (p 1)) (hg : g
 1 = p) : ↑(g • z) = (lcRow0 p ↑(g : SL(2, Real)) : Complex) / ((p 0 : Complex) 
^ 2 + (p 1 : Complex) ^ 2) + ((p 1 : Complex) * z - p 0) / (((p 0 : Complex) ^ 2
 + (p 1 : Complex) ^ 2) * (p 0 * z + p 1))
参数：hp : IsCoprime (p 0) (p 1)；hg : g 1 = p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `IsCoprime.sq_add_sq_ne_zero`：sq_add_sq_ne_zero {R : Type*} [CommRing R] 
[LinearOrder R] [IsStrictOrderedRing R] {a b : R} (h : IsCoprime a b) : a ^ 2 + 
b ^ 2 != 0
· 使用定理 `IsCoprime.ne_zero`：IsCoprime.ne_zero [Nontrivial R] {p : Fin 2 -> R} (h 
: IsCoprime (p 0) (p 1)) : p != 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `UpperHalfPlane.linear_ne_zero`：linear_ne_zero {cd : Fin 2 -> Real} (τ : 
ℍ) (h : cd != 0) : (cd 0 : Complex) * τ + cd 1 != 0
· 使用定理 `UpperHalfPlane.coe_specialLinearGroup_apply`：coe_specialLinearGroup_appl
y {R : Type*} [CommRing R] [Algebra R Real] (g : SL(2, R)) (z : ℍ) : ↑(g • z) = 
(((algebraMap R Real (g 0 0) : Co…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
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
（共 106 条，此处仅展示前 30 条）

--- 原说明 ---
This replaces `(g•z).re = a/c + *` in the standard theory with the following nov
el identity:
  `g • z = (a c + b d) / (c^2 + d^2) + (d z - c) / ((c^2 + d^2) (c z + d))`
  which does not need to be decomposed depending on whether `c = 0`.
-/
theorem smul_eq_lcRow0_add {p : Fin 2 → ℤ} (hp : IsCoprime (p 0) (p 1)) (hg : g 1 = p) :
    ↑(g • z) =
      (lcRow0 p ↑(g : SL(2, ℝ)) : ℂ) / ((p 0 : ℂ) ^ 2 + (p 1 : ℂ) ^ 2) +
        ((p 1 : ℂ) * z - p 0) / (((p 0 : ℂ) ^ 2 + (p 1 : ℂ) ^ 2) * (p 0 * z + p 1)) := by
  have nonZ1 : (p 0 : ℂ) ^ 2 + (p 1 : ℂ) ^ 2 ≠ 0 := mod_cast hp.sq_add_sq_ne_zero
  have : ((↑) : ℤ → ℝ) ∘ p ≠ 0 := fun h => hp.ne_zero (by ext i; simpa using congr_fun h i)
  have nonZ2 : (p 0 : ℂ) * z + p 1 ≠ 0 := by simpa using linear_ne_zero z this
  subst hg
  rw [coe_specialLinearGroup_apply]
  replace nonZ2 : z * (g 1 0 : ℂ) + g 1 1 ≠ 0 := by convert! nonZ2 using 1; ring
  have H := congr(Int.cast (R := ℂ) $(det_fin_two g))
  simp at H
  simp [field]
  linear_combination -((z : ℂ) * (g 1 1 : ℂ) - g 1 0) * H

set_option backward.isDefEq.respectTransparency false in
/-
**ModularGroup.tendsto_abs_re_smul** 是 Mathlib 中的一个定理，位于命名空间 `ModularGroup`。
形式化陈述：tendsto_abs_re_smul {p : Fin 2 -> Int} (hp : IsCoprime (p 0) (p 1)) : Tend
sto (fun g : { g : SL(2, Int) // g 1 = p } => |((g : SL(2, Int)) • z).re|) cofin
ite atTop
参数：hp : IsCoprime (p 0) (p 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsCoprime.sq_add_sq_ne_zero`：sq_add_sq_ne_zero {R : Type*} [CommRing R] 
[LinearOrder R] [IsStrictOrderedRing R] {a b : R} (h : IsCoprime a b) : a ^ 2 + 
b ^ 2 != 0
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用定理 `Int.cast_pow`：∀ {R : Type u_1} [inst : Ring R] (n : ℤ) (m : ℕ), ↑(n ^ m)
 = ↑n ^ m
· 使用定理 `Complex.ofReal_add`：ofReal_add (r s : Real) : ((r + s : Real) : Complex)
 = r + s
· 使用定理 `Complex.ofReal_pow`：ofReal_pow (r : Real) (n : Nat) : ((r ^ n : Real) : 
Complex) = (r : Complex) ^ n
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `ModularGroup.smul_eq_lcRow0_add`：smul_eq_lcRow0_add {p : Fin 2 -> Int} (
hp : IsCoprime (p 0) (p 1)) (hg : g 1 = p) : ↑(g • z) = (lcRow0 p ↑(g : SL(2, Re
al)) : Complex) / ((p…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Topology.IsClosedEmbedding.tendsto_cocompact`：Topology.IsClosedEmbedding
.tendsto_cocompact (hf : IsClosedEmbedding f) : Tendsto f (Filter.cocompact X) (
Filter.cocompact Y)
· 使用定理 `Homeomorph.isClosedEmbedding`：isClosedEmbedding (h : X ≃ₜ Y) : IsClosedE
mbedding h
（共 33 条，此处仅展示前 30 条）
-/
theorem tendsto_abs_re_smul {p : Fin 2 → ℤ} (hp : IsCoprime (p 0) (p 1)) :
    Tendsto
      (fun g : { g : SL(2, ℤ) // g 1 = p } => |((g : SL(2, ℤ)) • z).re|) cofinite atTop := by
  suffices
    Tendsto (fun g : (fun g : SL(2, ℤ) => g 1) ⁻¹' {p} => ((g : SL(2, ℤ)) • z).re) cofinite
      (cocompact ℝ)
    by exact tendsto_norm_cocompact_atTop.comp this
  have : ((p 0 : ℝ) ^ 2 + (p 1 : ℝ) ^ 2)⁻¹ ≠ 0 := by
    apply inv_ne_zero
    exact mod_cast hp.sq_add_sq_ne_zero
  let f := Homeomorph.mulRight₀ _ this
  let ff := Homeomorph.addRight
    (((p 1 : ℂ) * z - p 0) / (((p 0 : ℂ) ^ 2 + (p 1 : ℂ) ^ 2) * (p 0 * z + p 1))).re
  convert! (f.trans ff).isClosedEmbedding.tendsto_cocompact.comp (tendsto_lcRow0 hp) with _ _ g
  change
    ((g : SL(2, ℤ)) • z).re =
      lcRow0 p ↑(↑g : SL(2, ℝ)) / ((p 0 : ℝ) ^ 2 + (p 1 : ℝ) ^ 2) +
        Complex.re (((p 1 : ℂ) * z - p 0) / (((p 0 : ℂ) ^ 2 + (p 1 : ℂ) ^ 2) * (p 0 * z + p 1)))
  exact mod_cast congr_arg Complex.re (smul_eq_lcRow0_add z hp g.2)

end TendstoLemmas

section FundamentalDomain


attribute [local simp] UpperHalfPlane.coe_specialLinearGroup_apply

/-- For `z : ℍ`, there is a `g : SL(2,ℤ)` maximizing `(g•z).im` -/
/-
**ModularGroup.exists_max_im** 是 Mathlib 中的一个定理，位于命名空间 `ModularGroup`。
形式化陈述：exists_max_im : exists g : SL(2, Int), forall g' : SL(2, Int), (g' • z).im
 <= (g • z).im
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `isCoprime_one_left`：isCoprime_one_left : IsCoprime 1 x
· 使用定理 `Filter.Tendsto.exists_within_forall_le`：Filter.Tendsto.exists_within_for
all_le {α β : Type*} [LinearOrder β] {s : Set α} (hs : s.Nonempty) {f : α -> β} 
(hf : Filter.Tendsto f Filte…
· 使用定理 `ModularGroup.tendsto_normSq_coprime_pair`：tendsto_normSq_coprime_pair : 
Filter.Tendsto (fun p : Fin 2 -> Int => normSq ((p 0 : Complex) * z + p 1)) cofi
nite atTop
· 使用定理 `ModularGroup.bottom_row_surj`：bottom_row_surj {R : Type*} [CommRing R] :
 Set.SurjOn (fun g : SL(2, R) => (↑g : Matrix (Fin 2) (Fin 2) R) 1) Set.univ {cd
 | IsCoprime (cd 0…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ModularGroup.im_smul_eq_div_normSq`：im_smul_eq_div_normSq : (g • z).im =
 z.im / Complex.normSq (denom g z)
· 使用引理 `div_le_div_iff_of_pos_left`：div_le_div_iff_of_pos_left (ha : 0 < a) (hb 
: 0 < b) (hc : 0 < c) : a / b <= a / c ↔ c <= b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
· 使用定理 `UpperHalfPlane.normSq_denom_pos`：normSq_denom_pos (g : GL (Fin 2) Real) 
{z : Complex} (hz : z.im != 0) : 0 < Complex.normSq (denom g z)
· 使用定理 `UpperHalfPlane.im_ne_zero`：im_ne_zero (z : ℍ) : z.im != 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ModularGroup.bottom_row_coprime`：bottom_row_coprime {R : Type*} [CommRin
g R] (g : SL(2, R)) : IsCoprime ((↑g : Matrix (Fin 2) (Fin 2) R) 1 0) ((↑g : Mat
rix (Fin 2) (Fin 2) R…

--- 原说明 ---
For `z : ℍ`, there is a `g : SL(2,ℤ)` maximizing `(g•z).im`
-/
theorem exists_max_im : ∃ g : SL(2, ℤ), ∀ g' : SL(2, ℤ), (g' • z).im ≤ (g • z).im := by
  let s : Set (Fin 2 → ℤ) := {cd | IsCoprime (cd 0) (cd 1)}
  have hs : s.Nonempty := ⟨![1, 1], isCoprime_one_left⟩
  obtain ⟨p, hp_coprime, hp⟩ :=
    Filter.Tendsto.exists_within_forall_le hs (tendsto_normSq_coprime_pair z)
  obtain ⟨g, -, hg⟩ := bottom_row_surj hp_coprime
  refine ⟨g, fun g' => ?_⟩
  rw [ModularGroup.im_smul_eq_div_normSq, ModularGroup.im_smul_eq_div_normSq,
    div_le_div_iff_of_pos_left]
  · simpa [← hg] using! hp (g' 1) (bottom_row_coprime g')
  · exact z.im_pos
  · exact normSq_denom_pos g' z.im_ne_zero
  · exact normSq_denom_pos g z.im_ne_zero

/-- Given `z : ℍ` and a bottom row `(c,d)`, among the `g : SL(2,ℤ)` with this bottom row, minimize
  `|(g•z).re|`. -/
/-
**ModularGroup.exists_row_one_eq_and_min_re** 是 Mathlib 中的一个定理，位于命名空间 `ModularGr
oup`。
形式化陈述：exists_row_one_eq_and_min_re {cd : Fin 2 -> Int} (hcd : IsCoprime (cd 0) (
cd 1)) : exists g : SL(2, Int), g 1 = cd ∧ forall g' : SL(2, Int), g 1 = g' 1 ->
 |(g • z).re| <= |(g' • z).re|
参数：hcd : IsCoprime (cd 0) (cd 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ModularGroup.bottom_row_surj`：bottom_row_surj {R : Type*} [CommRing R] :
 Set.SurjOn (fun g : SL(2, R) => (↑g : Matrix (Fin 2) (Fin 2) R) 1) Set.univ {cd
 | IsCoprime (cd 0…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Filter.Tendsto.exists_forall_le`：Filter.Tendsto.exists_forall_le [Nonemp
ty α] [LinearOrder β] {f : α -> β} (hf : Tendsto f cofinite atTop) : exists a₀, 
forall a, f a₀ <= f a
· 使用定理 `ModularGroup.tendsto_abs_re_smul`：tendsto_abs_re_smul {p : Fin 2 -> Int}
 (hp : IsCoprime (p 0) (p 1)) : Tendsto (fun g : { g : SL(2, Int) // g 1 = p } =
> |((g : SL(2, Int)) •…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b

--- 原说明 ---
Given `z : ℍ` and a bottom row `(c,d)`, among the `g : SL(2,ℤ)` with this bottom
 row, minimize
  `|(g•z).re|`.
-/
theorem exists_row_one_eq_and_min_re {cd : Fin 2 → ℤ} (hcd : IsCoprime (cd 0) (cd 1)) :
    ∃ g : SL(2, ℤ), g 1 = cd ∧ ∀ g' : SL(2, ℤ), g 1 = g' 1 →
      |(g • z).re| ≤ |(g' • z).re| := by
  have : Nonempty { g : SL(2, ℤ) // g 1 = cd } :=
    let ⟨x, hx⟩ := bottom_row_surj hcd
    ⟨⟨x, hx.2⟩⟩
  obtain ⟨g, hg⟩ := Filter.Tendsto.exists_forall_le (tendsto_abs_re_smul z hcd)
  refine ⟨g, g.2, ?_⟩
  intro g1 hg1
  have : g1 ∈ (fun g : SL(2, ℤ) => g 1) ⁻¹' {cd} := by
    rw [Set.mem_preimage, Set.mem_singleton_iff]
    exact Eq.trans hg1.symm (Set.mem_singleton_iff.mp (Set.mem_preimage.mp g.2))
  exact hg ⟨g1, this⟩
/-
**ModularGroup.coe_T_zpow_smul_eq** 是 Mathlib 中的一个定理，位于命名空间 `ModularGroup`。
形式化陈述：coe_T_zpow_smul_eq {n : Int} : (↑(T ^ n • z) : Complex) = z + n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UpperHalfPlane.coe_specialLinearGroup_apply`：coe_specialLinearGroup_appl
y {R : Type*} [CommRing R] [Algebra R Real] (g : SL(2, R)) (z : ℍ) : ↑(g • z) = 
(((algebraMap R Real (g 0 0) : Co…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ModularGroup.coe_T_zpow`：coe_T_zpow (n : Int) : (T ^ n).1 = !![1, n; 0, 
1]
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_T_zpow_smul_eq {n : ℤ} : (↑(T ^ n • z) : ℂ) = z + n := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [coe_T_zpow, -map_zpow]
/-
**ModularGroup.re_T_zpow_smul** 是 Mathlib 中的一个定理，位于命名空间 `ModularGroup`。
形式化陈述：re_T_zpow_smul (n : Int) : (T ^ n • z).re = z.re + n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `UpperHalfPlane.coe_re`：coe_re (z : ℍ) : (z : Complex).re = z.re
· 使用定理 `ModularGroup.coe_T_zpow_smul_eq`：coe_T_zpow_smul_eq {n : Int} : (↑(T ^ n
 • z) : Complex) = z + n
· 使用定理 `Complex.add_re`：add_re (z w : Complex) : (z + w).re = z.re + w.re
· 使用定理 `Complex.intCast_re`：∀ (n : ℤ), (↑n).re = ↑n
-/
theorem re_T_zpow_smul (n : ℤ) : (T ^ n • z).re = z.re + n := by
  rw [← coe_re, coe_T_zpow_smul_eq, add_re, intCast_re, coe_re]
/-
**ModularGroup.im_T_zpow_smul** 是 Mathlib 中的一个定理，位于命名空间 `ModularGroup`。
形式化陈述：im_T_zpow_smul (n : Int) : (T ^ n • z).im = z.im
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `UpperHalfPlane.coe_im`：coe_im (z : ℍ) : (z : Complex).im = z.im
· 使用定理 `ModularGroup.coe_T_zpow_smul_eq`：coe_T_zpow_smul_eq {n : Int} : (↑(T ^ n
 • z) : Complex) = z + n
· 使用定理 `Complex.add_im`：add_im (z w : Complex) : (z + w).im = z.im + w.im
· 使用定理 `Complex.intCast_im`：∀ (n : ℤ), (↑n).im = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem im_T_zpow_smul (n : ℤ) : (T ^ n • z).im = z.im := by
  rw [← coe_im, coe_T_zpow_smul_eq, add_im, intCast_im, add_zero, coe_im]
/-
**ModularGroup.re_T_smul** 是 Mathlib 中的一个定理，位于命名空间 `ModularGroup`。
形式化陈述：re_T_smul : (T • z).re = z.re + 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `ModularGroup.re_T_zpow_smul`：re_T_zpow_smul (n : Int) : (T ^ n • z).re =
 z.re + n
-/
theorem re_T_smul : (T • z).re = z.re + 1 := by simpa using re_T_zpow_smul z 1
/-
**ModularGroup.im_T_smul** 是 Mathlib 中的一个定理，位于命名空间 `ModularGroup`。
形式化陈述：im_T_smul : (T • z).im = z.im
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `ModularGroup.im_T_zpow_smul`：im_T_zpow_smul (n : Int) : (T ^ n • z).im =
 z.im
-/
theorem im_T_smul : (T • z).im = z.im := by simpa using im_T_zpow_smul z 1
/-
**ModularGroup.re_T_inv_smul** 是 Mathlib 中的一个定理，位于命名空间 `ModularGroup`。
形式化陈述：re_T_inv_smul : (T⁻¹ • z).re = z.re - 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `ModularGroup.re_T_zpow_smul`：re_T_zpow_smul (n : Int) : (T ^ n • z).re =
 z.re + n
-/
theorem re_T_inv_smul : (T⁻¹ • z).re = z.re - 1 := by simpa using! re_T_zpow_smul z (-1)
/-
**ModularGroup.im_T_inv_smul** 是 Mathlib 中的一个定理，位于命名空间 `ModularGroup`。
形式化陈述：im_T_inv_smul : (T⁻¹ • z).im = z.im
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `ModularGroup.im_T_zpow_smul`：im_T_zpow_smul (n : Int) : (T ^ n • z).im =
 z.im
-/
theorem im_T_inv_smul : (T⁻¹ • z).im = z.im := by simpa using im_T_zpow_smul z (-1)

variable {z}

-- If instead we had `g` and `T` of type `PSL(2, ℤ)`, then we could simply state `g = T^n`.
/-
**ModularGroup.exists_eq_T_zpow_of_c_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `ModularG
roup`。
形式化陈述：exists_eq_T_zpow_of_c_eq_zero (hc : g 1 0 = 0) : exists n : Int, forall z 
: ℍ, g • z = T ^ n • z
参数：hc : g 1 0 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Matrix.SpecialLinearGroup.det_coe`：det_coe : det ↑ₘA = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det_fin_two`：det_fin_two (A : Matrix (Fin 2) (Fin 2) R) : det A =
 A 0 0 * A 1 1 - A 0 1 * A 1 0
· 使用引理 `Int.eq_one_or_neg_one_of_mul_eq_one'`：eq_one_or_neg_one_of_mul_eq_one' (
h : u * v = 1) : u = 1 ∧ v = 1 ∨ u = -1 ∧ v = -1
· 使用定理 `Matrix.SpecialLinearGroup.ext`：ext (A B : SpecialLinearGroup n R) : (for
all i j, A i j = B i j) -> A = B
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `ModularGroup.coe_T_zpow`：coe_T_zpow (n : Int) : (T ^ n).1 = !![1, n; 0, 
1]
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `Matrix.adjugate_fin_two_of`：adjugate_fin_two_of (a b c d : α) : adjugate
 !![a, b; c, d] = !![d, -b; -c, a]
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `ModularGroup.SL_neg_smul`：SL_neg_smul : -g • z = g • z
-/
theorem exists_eq_T_zpow_of_c_eq_zero (hc : g 1 0 = 0) :
    ∃ n : ℤ, ∀ z : ℍ, g • z = T ^ n • z := by
  have had := g.det_coe
  replace had : g 0 0 * g 1 1 = 1 := by rw [det_fin_two, hc] at had; lia
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' had with (⟨ha, hd⟩ | ⟨ha, hd⟩)
  · use g 0 1
    suffices g = T ^ g 0 1 by intro z; conv_lhs => rw [this]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [ha, hc, hd, coe_T_zpow, show (1 : Fin (0 + 2)) = (1 : Fin 2) from rfl]
  · use -(g 0 1)
    suffices g = -T ^ (-(g 0 1)) by intro z; conv_lhs => rw [this, SL_neg_smul]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [ha, hc, hd, coe_T_zpow, show (1 : Fin (0 + 2)) = (1 : Fin 2) from rfl]

-- If `c = 1`, then `g` factorises into a product terms involving only `T` and `S`.
/-
**ModularGroup.g_eq_of_c_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `ModularGroup`。
形式化陈述：g_eq_of_c_eq_one (hc : g 1 0 = 1) : g = T ^ g 0 0 * S * T ^ g 1 1
参数：hc : g 1 0 = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.SpecialLinearGroup.det_coe`：det_coe : det ↑ₘA = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det_fin_two`：det_fin_two (A : Matrix (Fin 2) (Fin 2) R) : det A =
 A 0 0 * A 1 1 - A 0 1 * A 1 0
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.eta_fin_two`：eta_fin_two (A : Matrix (Fin 2) (Fin 2) α) : A = !![
A 0 0, A 0 1; A 1 0, A 1 1]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `ModularGroup.coe_T_zpow`：coe_T_zpow (n : Int) : (T ^ n).1 = !![1, n; 0, 
1]
· 使用定理 `Matrix.mul_fin_two`：mul_fin_two [AddCommMonoid α] [Mul α] (a₁₁ a₁₂ a₂₁ a
₂₂ b₁₁ b₁₂ b₂₁ b₂₂ : α) : !![a₁₁, a₁₂; a₂₁, a₂₂] * !![b₁₁, b₁₂; b₂₁, b₂₂] = !![a
₁₁ * b₁₁…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem g_eq_of_c_eq_one (hc : g 1 0 = 1) : g = T ^ g 0 0 * S * T ^ g 1 1 := by
  have hg := g.det_coe.symm
  replace hg : g 0 1 = g 0 0 * g 1 1 - 1 := by rw [det_fin_two, hc] at hg; lia
  refine Subtype.ext ?_
  conv_lhs => rw [(g : Matrix _ _ ℤ).eta_fin_two]
  simp only [hg, sub_eq_add_neg, hc, coe_mul, coe_T_zpow, coe_S, mul_fin_two, mul_zero, mul_one,
    zero_add, one_mul, add_zero, zero_mul]

/-- If `1 < |z|`, then `|S • z| < 1`. -/
/-
**ModularGroup.normSq_S_smul_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `ModularGroup`。
形式化陈述：normSq_S_smul_lt_one (h : 1 < normSq z) : normSq ↑(S • z) < 1
参数：h : 1 < normSq z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UpperHalfPlane.coe_specialLinearGroup_apply`：coe_specialLinearGroup_appl
y {R : Type*} [CommRing R] [Algebra R Real] (g : SL(2, R)) (z : ℍ) : ↑(g • z) = 
(((algebraMap R Real (g 0 0) : Co…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `Complex.normSq_neg`：normSq_neg (z : Complex) : normSq (-z) = normSq z
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `inv_lt_inv₀`：inv_lt_inv₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ < b⁻¹ ↔ b < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
If `1 < |z|`, then `|S • z| < 1`.
-/
theorem normSq_S_smul_lt_one (h : 1 < normSq z) : normSq ↑(S • z) < 1 := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simpa [coe_S, num, denom] using (inv_lt_inv₀ z.normSq_pos zero_lt_one).mpr h

/-- If `|z| < 1`, then applying `S` strictly decreases `im`. -/
/-
**ModularGroup.im_lt_im_S_smul** 是 Mathlib 中的一个定理，位于命名空间 `ModularGroup`。
形式化陈述：im_lt_im_S_smul (h : normSq z < 1) : z.im < (S • z).im
参数：h : normSq z < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ModularGroup.im_smul_eq_div_normSq`：im_smul_eq_div_normSq : (g • z).im =
 z.im / Complex.normSq (denom g z)
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `lt_div_iff₀`：lt_div_iff₀ (hc : 0 < c) : a < b / c ↔ a * c < b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `UpperHalfPlane.normSq_pos`：normSq_pos (z : ℍ) : 0 < Complex.normSq (z : 
Complex)
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
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
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
（共 75 条，此处仅展示前 30 条）

--- 原说明 ---
If `|z| < 1`, then applying `S` strictly decreases `im`.
-/
theorem im_lt_im_S_smul (h : normSq z < 1) : z.im < (S • z).im := by
  rw [ModularGroup.im_smul_eq_div_normSq]
  have : z.im < z.im / normSq (z : ℂ) := by
    have imz : 0 < z.im := im_pos z
    apply (lt_div_iff₀ z.normSq_pos).mpr
    nlinarith
  simpa [denom, coe_S, SpecialLinearGroup.toGL]

/-- The standard (closed) fundamental domain of the action of `SL(2,ℤ)` on `ℍ`. -/
/-
**ModularGroup.fd** 是 Mathlib 中的一个定义，位于命名空间 `ModularGroup`。
形式化陈述：fd : Set ℍ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The standard (closed) fundamental domain of the action of `SL(2,ℤ)` on `ℍ`.
-/
def fd : Set ℍ :=
  {z | 1 ≤ normSq (z : ℂ) ∧ |z.re| ≤ (1 : ℝ) / 2}

/-- The standard open fundamental domain of the action of `SL(2,ℤ)` on `ℍ`. -/
/-
**ModularGroup.fdo** 是 Mathlib 中的一个定义，位于命名空间 `ModularGroup`。
形式化陈述：fdo : Set ℍ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The standard open fundamental domain of the action of `SL(2,ℤ)` on `ℍ`.
-/
def fdo : Set ℍ :=
  {z | 1 < normSq (z : ℂ) ∧ |z.re| < (1 : ℝ) / 2}

@[inherit_doc ModularGroup.fd]
scoped[Modular] notation "𝒟" => ModularGroup.fd

@[inherit_doc ModularGroup.fdo]
scoped[Modular] notation "𝒟ᵒ" => ModularGroup.fdo

open scoped Modular
/-
**ModularGroup.fdo_subset_fd** 是 Mathlib 中的一个引理，位于命名空间 `ModularGroup`。
形式化陈述：fdo_subset_fd : 𝒟ᵒ subseteq 𝒟
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma fdo_subset_fd : 𝒟ᵒ ⊆ 𝒟 := fun _ ⟨hx, hx'⟩ ↦ ⟨hx.le, hx'.le⟩
/-
**ModularGroup.** 是 Mathlib 中的一个引理，位于命名空间 `ModularGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ρ_mem_fd : ρ ∈ 𝒟 := by
  constructor <;> norm_num [ρ, ← pow_two, div_pow]
/-
**ModularGroup.I_mem_fd** 是 Mathlib 中的一个引理，位于命名空间 `ModularGroup`。
形式化陈述：I_mem_fd : I in 𝒟
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.normSq_I`：normSq_I : normSq I = 1
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `UpperHalfPlane.I_re`：I_re : I.re = 0
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_eq`：∀ {α : Type u_1} [inst : DivisionSem
iring α] {n d : ℕ} {a n' d' : α},   Mathlib.Meta.NormNum.IsNNRat a n d → ↑n = n'
 → ↑d = d' → a = n' / d'
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.isRat_le_true`：isRat_le_true [Ring α] [LinearOrder 
α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Int} -> {da db : Nat} -> IsRa
t a na da -> IsRat b nb …
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isRat`：∀ {α : Type u_1} [inst : Ring α] 
{a : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n d → Mathlib.Meta.NormNum.I
sRat a (Int.ofNat n) d
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
-/
lemma I_mem_fd : I ∈ 𝒟 := by
  constructor <;> norm_num
/-
**ModularGroup.abs_two_mul_re_lt_one_of_mem_fdo** 是 Mathlib 中的一个定理，位于命名空间 `Modul
arGroup`。
形式化陈述：abs_two_mul_re_lt_one_of_mem_fdo (h : z in 𝒟ᵒ) : |2 * z.re| < 1
参数：h : z in 𝒟ᵒ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用引理 `abs_two`：abs_two : |(2 : α)| = 2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `lt_div_iff₀'`：lt_div_iff₀' (hc : 0 < c) : a < b / c ↔ c * a < b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `zero_lt_two'`：zero_lt_two' : (0 : α) < 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem abs_two_mul_re_lt_one_of_mem_fdo (h : z ∈ 𝒟ᵒ) : |2 * z.re| < 1 := by
  rw [abs_mul, abs_two, ← lt_div_iff₀' (zero_lt_two' ℝ)]
  exact h.2
/-
**ModularGroup.three_lt_four_mul_im_sq_of_mem_fdo** 是 Mathlib 中的一个定理，位于命名空间 `Mod
ularGroup`。
形式化陈述：three_lt_four_mul_im_sq_of_mem_fdo (h : z in 𝒟ᵒ) : 3 < 4 * z.im ^ 2
参数：h : z in 𝒟ᵒ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `abs_cases`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrde
r G] [IsOrderedAddMonoid G] (a : G),   |a| = a ∧ 0 ≤ a ∨ |a| = -a ∧ a < 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pp_pf_overlap`：∀ {R : Type u_1} [inst : C
ommSemiring R] {a₂ b₂ c : R} {ea eb e : ℕ} (x : R),   ea + eb = e → a₂ * b₂ = c 
→ x ^ ea * a₂ * (x ^ eb * b₂) = x …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
（共 99 条，此处仅展示前 30 条）
-/
theorem three_lt_four_mul_im_sq_of_mem_fdo (h : z ∈ 𝒟ᵒ) : 3 < 4 * z.im ^ 2 := by
  have : 1 < z.re * z.re + z.im * z.im := by simpa [Complex.normSq_apply] using h.1
  have := h.2
  cases abs_cases z.re <;> nlinarith

/-- non-strict variant of `ModularGroup.three_le_four_mul_im_sq_of_mem_fdo` -/
/-
**ModularGroup.three_le_four_mul_im_sq_of_mem_fd** 是 Mathlib 中的一个定理，位于命名空间 `Modu
larGroup`。
形式化陈述：three_le_four_mul_im_sq_of_mem_fd {τ : ℍ} (h : τ in 𝒟) : 3 <= 4 * τ.im ^ 2
参数：h : τ in 𝒟。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `abs_cases`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrde
r G] [IsOrderedAddMonoid G] (a : G),   |a| = a ∧ 0 ≤ a ∨ |a| = -a ∧ a < 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pp_pf_overlap`：∀ {R : Type u_1} [inst : C
ommSemiring R] {a₂ b₂ c : R} {ea eb e : ℕ} (x : R),   ea + eb = e → a₂ * b₂ = c 
→ x ^ ea * a₂ * (x ^ eb * b₂) = x …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
（共 94 条，此处仅展示前 30 条）

--- 原说明 ---
non-strict variant of `ModularGroup.three_le_four_mul_im_sq_of_mem_fdo`
-/
theorem three_le_four_mul_im_sq_of_mem_fd {τ : ℍ} (h : τ ∈ 𝒟) : 3 ≤ 4 * τ.im ^ 2 := by
  have : 1 ≤ τ.re * τ.re + τ.im * τ.im := by simpa [Complex.normSq_apply] using h.1
  cases abs_cases τ.re <;> nlinarith [h.2]

/-- If `z ∈ 𝒟ᵒ`, and `n : ℤ`, then `|z + n| > 1`. -/
/-
**ModularGroup.one_lt_normSq_T_zpow_smul** 是 Mathlib 中的一个定理，位于命名空间 `ModularGroup
`。
形式化陈述：one_lt_normSq_T_zpow_smul (hz : z in 𝒟ᵒ) (n : Int) : 1 < normSq (T ^ n • z
 : ℍ)
参数：hz : z in 𝒟ᵒ；n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ModularGroup.coe_T_zpow_smul_eq`：coe_T_zpow_smul_eq {n : Int} : (↑(T ^ n
 • z) : Complex) = z + n
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Int.nneg_mul_add_sq_of_abs_le_one`：nneg_mul_add_sq_of_abs_le_one (n : In
t) (hx : |x| <= 1) : (0 : R) <= n * x + n * n
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `ModularGroup.abs_two_mul_re_lt_one_of_mem_fdo`：abs_two_mul_re_lt_one_of_
mem_fdo (h : z in 𝒟ᵒ) : |2 * z.re| < 1
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pp_pf_overlap`：∀ {R : Type u_1} [inst : C
ommSemiring R] {a₂ b₂ c : R} {ea eb e : ℕ} (x : R),   ea + eb = e → a₂ * b₂ = c 
→ x ^ ea * a₂ * (x ^ eb * b₂) = x …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
（共 57 条，此处仅展示前 30 条）

--- 原说明 ---
If `z ∈ 𝒟ᵒ`, and `n : ℤ`, then `|z + n| > 1`.
-/
theorem one_lt_normSq_T_zpow_smul (hz : z ∈ 𝒟ᵒ) (n : ℤ) : 1 < normSq (T ^ n • z : ℍ) := by
  rw [coe_T_zpow_smul_eq]
  have hz₁ : 1 < z.re * z.re + z.im * z.im := hz.1
  have hzn := Int.nneg_mul_add_sq_of_abs_le_one n (abs_two_mul_re_lt_one_of_mem_fdo hz).le
  have : 1 < (z.re + ↑n) * (z.re + ↑n) + z.im * z.im := by linarith
  simpa [normSq, num, denom]
/-
**ModularGroup.eq_zero_of_mem_fdo_of_T_zpow_mem_fdo** 是 Mathlib 中的一个定理，位于命名空间 `M
odularGroup`。
形式化陈述：eq_zero_of_mem_fdo_of_T_zpow_mem_fdo {n : Int} (hz : z in 𝒟ᵒ) (hg : T ^ n 
• z in 𝒟ᵒ) : n = 0
参数：hz : z in 𝒟ᵒ；hg : T ^ n • z in 𝒟ᵒ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `abs_add'`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrder
 G] [IsOrderedAddMonoid G] (a b : G), |a| ≤ |b| + |b + a|
· 使用定理 `add_lt_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftStrictMono α] [AddRightStrictMono α] {a b c d : α},   a < b → c < d → a + c < 
…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ModularGroup.re_T_zpow_smul`：re_T_zpow_smul (n : Int) : (T ^ n • z).re =
 z.re + n
· 使用定理 `add_halves`：∀ {K : Type u_1} [inst : DivisionSemiring K] [NeZero 2] (a :
 K), a / 2 + a / 2 = a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Int.abs_lt_one_iff`：abs_lt_one_iff {a : Int} : |a| < 1 ↔ a = 0
· 使用定理 `Int.cast_lt`：∀ {R : Type u_1} [inst : AddCommGroupWithOne R] [inst_1 : P
artialOrder R] [AddLeftMono R] [ZeroLEOneClass R] [NeZero 1]   {m n : ℤ}, ↑m < ↑
n…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用引理 `Int.cast_abs`：cast_abs : (↑|a| : R) = |(a : R)|
-/
theorem eq_zero_of_mem_fdo_of_T_zpow_mem_fdo {n : ℤ} (hz : z ∈ 𝒟ᵒ) (hg : T ^ n • z ∈ 𝒟ᵒ) :
    n = 0 := by
  suffices |(n : ℝ)| < 1 by
    rwa [← Int.cast_abs, ← Int.cast_one, Int.cast_lt, Int.abs_lt_one_iff] at this
  have h₁ := hz.2
  have h₂ := hg.2
  rw [re_T_zpow_smul] at h₂
  calc
    |(n : ℝ)| ≤ |z.re| + |z.re + (n : ℝ)| := abs_add' (n : ℝ) z.re
    _ < 1 / 2 + 1 / 2 := add_lt_add h₁ h₂
    _ = 1 := add_halves 1

/-- First Fundamental Domain Lemma: Any `z : ℍ` can be moved to `𝒟` by an element of
`SL(2,ℤ)` -/
/-
**ModularGroup.exists_smul_mem_fd** 是 Mathlib 中的一个定理，位于命名空间 `ModularGroup`。
形式化陈述：exists_smul_mem_fd (z : ℍ) : exists g : SL(2, Int), g • z in 𝒟
参数：z : ℍ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModularGroup.exists_max_im`：exists_max_im : exists g : SL(2, Int), foral
l g' : SL(2, Int), (g' • z).im <= (g • z).im
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ModularGroup.exists_row_one_eq_and_min_re`：exists_row_one_eq_and_min_re 
{cd : Fin 2 -> Int} (hcd : IsCoprime (cd 0) (cd 1)) : exists g : SL(2, Int), g 1
 = cd ∧ forall g' : SL(2, Int),…
· 使用定理 `ModularGroup.bottom_row_coprime`：bottom_row_coprime {R : Type*} [CommRin
g R] (g : SL(2, R)) : IsCoprime ((↑g : Matrix (Fin 2) (Fin 2) R) 1 0) ((↑g : Mat
rix (Fin 2) (Fin 2) R…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ModularGroup.im_smul_eq_div_normSq`：im_smul_eq_div_normSq : (g • z).im =
 z.im / Complex.normSq (denom g z)
· 使用定理 `ModularGroup.denom_apply`：denom_apply : denom g z = g 1 0 * z + g 1 1
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `ModularGroup.im_lt_im_S_smul`：im_lt_im_S_smul (h : normSq z < 1) : z.im 
< (S • z).im
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `abs_le`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrder G
] [IsOrderedAddMonoid G] {a b : G},   |a| ≤ b ↔ -b ≤ a ∧ a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ModularGroup.T_mul_apply_one`：T_mul_apply_one (g : SL(2, Int)) : (T * g)
 1 = g 1
· 使用定理 `ModularGroup.re_T_smul`：re_T_smul : (T • z).re = z.re + 1
· 使用定理 `abs_cases`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrde
r G] [IsOrderedAddMonoid G] (a : G),   |a| = a ∧ 0 ≤ a ∨ |a| = -a ∧ a < 0
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
（共 96 条，此处仅展示前 30 条）

--- 原说明 ---
First Fundamental Domain Lemma: Any `z : ℍ` can be moved to `𝒟` by an element of
`SL(2,ℤ)`
-/
theorem exists_smul_mem_fd (z : ℍ) : ∃ g : SL(2, ℤ), g • z ∈ 𝒟 := by
  -- obtain a g₀ which maximizes im (g • z),
  obtain ⟨g₀, hg₀⟩ := exists_max_im z
  -- then among those, minimize re
  obtain ⟨g, hg, hg'⟩ := exists_row_one_eq_and_min_re z (bottom_row_coprime g₀)
  refine ⟨g, ?_⟩
  -- `g` has same max im property as `g₀`
  have hg₀' : ∀ g' : SL(2, ℤ), (g' • z).im ≤ (g • z).im := by
    have hg'' : (g • z).im = (g₀ • z).im := by
      rw [ModularGroup.im_smul_eq_div_normSq, ModularGroup.im_smul_eq_div_normSq,
        denom_apply, denom_apply, hg]
    simpa only [hg''] using hg₀
  constructor
  · -- Claim: `1 ≤ ⇑norm_sq ↑(g • z)`. If not, then `S•g•z` has larger imaginary part
    contrapose! hg₀'
    refine ⟨S * g, ?_⟩
    rw [mul_smul]
    exact im_lt_im_S_smul hg₀'
  · change |(g • z).re| ≤ 1 / 2
    -- if not, then either `T` or `T'` decrease |Re|.
    rw [abs_le]
    constructor
    · contrapose! hg'
      refine ⟨T * g, (T_mul_apply_one _).symm, ?_⟩
      rw [mul_smul, re_T_smul]
      cases abs_cases ((g • z).re + 1) <;> cases abs_cases (g • z).re <;> linarith
    · contrapose! hg'
      refine ⟨T⁻¹ * g, (T_inv_mul_apply_one _).symm, ?_⟩
      rw [mul_smul, re_T_inv_smul]
      cases abs_cases ((g • z).re - 1) <;> cases abs_cases (g • z).re <;> linarith

section UniqueRepresentative

/-- An auxiliary result en route to `ModularGroup.c_eq_zero` and `cases_of_mem_fd_smul_mem_fd`. -/
/-
**ModularGroup.abs_c_le_one** 是 Mathlib 中的一个定理，位于命名空间 `ModularGroup`。
形式化陈述：abs_c_le_one (hz : z in 𝒟) (hg : g • z in 𝒟) : |g 1 0| <= 1
参数：hz : z in 𝒟；hg : g • z in 𝒟。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `ModularGroup.three_le_four_mul_im_sq_of_mem_fd`：three_le_four_mul_im_sq_
of_mem_fd {τ : ℍ} (h : τ in 𝒟) : 3 <= 4 * τ.im ^ 2
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `Even.pow_nonneg`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : LinearOr
der R] [IsOrderedRing R] [ExistsAddOfLE R] {n : ℕ},   Even n → ∀ (a : R), 0 ≤ a 
^ n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用引理 `even_two_mul`：even_two_mul (a : α) : Even (2 * a)
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用引理 `div_le_one_of_le₀`：div_le_one_of_le₀ [ZeroLEOneClass G₀] (h : a <= b) (h
b : 0 <= b) : a / b <= 1
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用引理 `pow_four_le_pow_two_of_pow_two_le`：pow_four_le_pow_two_of_pow_two_le {a 
b : R} (h : a ^ 2 <= b) : a ^ 4 <= b ^ 2
· 使用定理 `UpperHalfPlane.c_mul_im_sq_le_normSq_denom`：c_mul_im_sq_le_normSq_denom 
: (g 1 0 * z.im) ^ 2 <= Complex.normSq (denom g z)
（共 111 条，此处仅展示前 30 条）

--- 原说明 ---
An auxiliary result en route to `ModularGroup.c_eq_zero` and `cases_of_mem_fd_sm
ul_mem_fd`.
-/
theorem abs_c_le_one (hz : z ∈ 𝒟) (hg : g • z ∈ 𝒟) : |g 1 0| ≤ 1 := by
  let c' : ℤ := g 1 0
  let c := (c' : ℝ)
  suffices 3 * c ^ 2 ≤ 4 by
    rw [← Int.cast_pow, ← Int.cast_three, ← Int.cast_four, ← Int.cast_mul, Int.cast_le] at this
    replace this : c' ^ 2 ≤ 1 ^ 2 := by lia
    rwa [sq_le_sq, abs_one] at this
  suffices c ≠ 0 → 9 * c ^ 4 ≤ 16 by
    rcases eq_or_ne c 0 with (hc | hc)
    · simp [hc]
    · apply le_of_sq_le_sq <;> grind
  intro hc
  have h₁ : 3 * 3 * c ^ 4 ≤ 4 * (g • z).im ^ 2 * (4 * z.im ^ 2) * c ^ 4 := by
    gcongr <;> exact three_le_four_mul_im_sq_of_mem_fd (by assumption)
  have h₂ : (c * z.im) ^ 4 / normSq (denom (↑g) z) ^ 2 ≤ 1 :=
    div_le_one_of_le₀
      (pow_four_le_pow_two_of_pow_two_le (z.c_mul_im_sq_le_normSq_denom g)) (sq_nonneg _)
  calc
    9 * c ^ 4 ≤ c ^ 4 * z.im ^ 2 * (g • z).im ^ 2 * 16 := by linarith
    _ = c ^ 4 * z.im ^ 4 / normSq (denom g z) ^ 2 * 16 := by grind [im_smul_eq_div_normSq]
    _ ≤ 16 := by rw [← mul_pow]; linarith

/-- Classify cases when `z ∈ 𝒟` and `g • z ∈ 𝒟` such that `c = 0`. -/
/-
**ModularGroup.cases_c_zero** 是 Mathlib 中的一个引理，位于命名空间 `ModularGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Classify cases when `z ∈ 𝒟` and `g • z ∈ 𝒟` such that `c = 0`.
-/
private lemma cases_c_zero (hz : z ∈ 𝒟) (hg : g • z ∈ 𝒟) (hc : g 1 0 = 0) :
    ((g = T ∨ g = -T) ∧ z.re = -1 / 2) ∨
    ((g = T⁻¹ ∨ g = -T⁻¹) ∧ z.re = 1 / 2) ∨
    (g = 1 ∨ g = -1) := by
  wlog hd : 0 ≤ g 1 1
  · specialize this hz (g := -g) (SL_neg_smul g z ▸ hg) (by simpa using hc) ?_
    · simpa using (not_le.mp hd).le
    convert! this using 2 <;> simp [neg_eq_iff_eq_neg, or_comm]
  have hd' : g 1 1 = 1 ∨ g 1 1 = -1 := by
    simpa [hc, isCoprime_zero_left, Int.isUnit_iff] using bottom_row_coprime g
  replace hd : g 1 1 = 1 := by grind
  have ha : g 0 0 = 1 := by grind [det_fin_two, g.property]
  let b := g 0 1
  have hgz : g = T ^ b := by
    ext i j
    rw [coe_T_zpow]
    fin_cases i <;> fin_cases j <;> tauto
  have hre : (g • z).re = b + z.re := by
    rw [hgz, ← coe_re, coe_T_zpow_smul_eq, add_re, coe_re, intCast_re, add_comm]
  have := (abs_sub_abs_le_abs_add ..).trans (hre ▸ hg.2)
  grw [sub_le_iff_le_add, hz.2, add_halves, ← Int.cast_abs, ← Int.cast_one, Int.cast_le,
    Int.abs_le_one_iff] at this
  rcases this with hb | hb | hb <;> rw [hb] at hgz
  · rw [hgz]
    simp
  · left
    rw [hgz, zpow_one, eq_self_iff_true, true_or, true_and]
    rw [hb, Int.cast_one] at hre
    linarith [(le_abs_self _).trans (abs_neg z.re ▸ hz.2), (le_abs_self _).trans hg.2]
  · right
    left
    rw [hgz, zpow_neg_one, eq_self_iff_true, true_or, true_and]
    rw [hb, Int.cast_neg, Int.cast_one] at hre
    linarith [(le_abs_self _).trans hz.2, (le_abs_self _).trans (abs_neg (g • z).re ▸ hg.2)]

/-- Classify possible `d` when `c = 1`. -/
/-
**ModularGroup.cases_d_of_c_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `ModularGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Classify possible `d` when `c = 1`.
-/
private lemma cases_d_of_c_eq_one (hz : z ∈ 𝒟) (hg' : ‖denom g z‖ ≤ 1) (hc : g 1 0 = 1) :
    |g 1 1| ≤ 1 := by
  have : ‖(z : ℂ) + g 1 1‖ ≤ 1 := by simpa [denom, hc] using hg'
  have := (abs_re_le_norm _).trans this
  rw [add_re, intCast_re, add_comm, coe_re] at this
  have := (abs_sub_abs_le_abs_add ..).trans this
  grw [sub_le_iff_le_add, hz.2, ← Int.cast_abs, ← Int.le_floor] at this
  convert! this
  rw [eq_comm, Int.floor_eq_iff]
  norm_num

/-- Classify possible `g, z` assuming `c = 1, d = 0`. -/
/-
**ModularGroup.cases_c_one_d_zero** 是 Mathlib 中的一个引理，位于命名空间 `ModularGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Classify possible `g, z` assuming `c = 1, d = 0`.
-/
private lemma cases_c_one_d_zero (hz : z ∈ 𝒟) (hg : g • z ∈ 𝒟) (hg' : ‖denom g z‖ ≤ 1)
    (hc : g 1 0 = 1) (hd : g 1 1 = 0) :
    (g = S ∧ ‖(z : ℂ)‖ = 1) ∨ (g = T⁻¹ * S ∧ z = ρ) ∨ (g = T * S ∧ z = (1 : ℝ) +ᵥ ρ) := by
  have hb : g 0 1 = -1 := by
    simpa [-SpecialLinearGroup.det_coe, det_fin_two, hd, hc, neg_eq_iff_eq_neg] using g.property
  have hz' : ‖(z : ℂ)‖ = 1 :=
    le_antisymm (by simpa [denom, hc, hd] using hg') (one_le_normSq_iff.mp hz.1)
  have hg' : g = T ^ g 0 0 * S := by
    ext i j
    simp only [coe_mul, coe_S, coe_T_zpow, Matrix.mul_fin_two, mul_zero, mul_one, zero_add,
      one_mul, add_zero, zero_mul]
    fin_cases i <;> fin_cases j <;> tauto
  rw [hg', mul_smul] at hg
  have hSre : re (S • z) = -z.re := by
    rw [modular_S_smul, ← coe_re, coe_mk, inv_re, normSq_eq_norm_sq, norm_neg, hz', one_pow,
      div_one, neg_re, coe_re]
  have := hg.2
  rw [← coe_re, coe_T_zpow_smul_eq, add_re, intCast_re, add_comm, coe_re, hSre] at this
  have := (abs_sub_abs_le_abs_add _ _).trans this
  rw [abs_neg, sub_le_iff_le_add] at this
  rcases lt_or_eq_of_le hz.2 with hzre | hzre
  · have := this.trans_lt ((add_lt_add_iff_left _).mpr hzre)
    rw [add_halves, ← Int.cast_abs, ← Int.cast_one (R := ℝ), Int.cast_lt] at this
    grind [Int.abs_lt_one_iff, zpow_zero]
  · rw [hzre, add_halves, ← Int.cast_abs, ← Int.cast_one (R := ℝ), Int.cast_le,
      Int.abs_le_one_iff] at this
    rcases this with h | h | h <;> simp only [h, Int.cast_zero, zero_add, Int.cast_one] at this
    · grind [zpow_zero]
    · rcases (abs_eq one_half_pos.le).mp hzre with hzre | hzre <;> [skip; norm_num [hzre] at this]
      rw [h, zpow_one] at hg'
      refine .inr <| .inr ⟨hg', eq_of_re_of_norm (by norm_num [hzre, ρ]) ?_⟩
      simp [hz', show 1 + (ρ : ℂ) = -ρ ^ 2 by grind [ρ_sq], norm_ρ]
    · rw [abs_eq (by norm_num)] at hzre
      rcases hzre with hzre | hzre <;> [norm_num [hzre] at this; skip]
      rw [h, zpow_neg_one] at hg'
      exact .inr <| .inl ⟨hg', eq_of_re_of_norm (by norm_num [hzre, ρ]) (by rw [hz', norm_ρ])⟩
/-
**ModularGroup.case_c_one_d_one** 是 Mathlib 中的一个引理，位于命名空间 `ModularGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma case_c_one_d_one (hz : z ∈ 𝒟) (hg : g • z ∈ 𝒟) (hg' : ‖denom g z‖ ≤ 1)
    (hc : g 1 0 = 1) (hd : g 1 1 = 1) :
    (g = S * T ∨ g = T * S * T) ∧ z = ρ := by
  have hgeq : g = T ^ g 0 0 * S * T := by
    refine Subtype.ext ?_
    rw [coe_mul, coe_mul, coe_T_zpow, coe_S, coe_T, mul_fin_two, mul_fin_two]
    ring_nf
    ext i j
    fin_cases i <;> fin_cases j <;> [tauto; simp; tauto; tauto]
    grind [g.property, det_fin_two]
  rw [hgeq]
  obtain ⟨hnorm, hre⟩ : normSq z = 1 ∧ z.re = -1 / 2 := by
    have hnorm : normSq ((z : ℂ) + 1) ≤ 1 := by simpa [denom, hc, hd, norm_def] using hg'
    have : normSq (z + 1) = normSq z + (2 * z.re + 1) := by simp [normSq]; ring
    rw [this] at hnorm
    constructor <;> linarith [hz.1, show 0 ≤ 2 * z.re + 1 by linarith [(neg_le_abs _).trans hz.2]]
  have hρ : z = ρ := by
    apply eq_of_re_of_norm
    · simp [hre, ρ]
    · rw [norm_def, hnorm, norm_ρ, Real.sqrt_one]
  refine ⟨?_, hρ⟩
  have hSTρ : (S * T) • ρ = ρ := by
    rw [mul_smul, ← SL_neg_smul S, ← S_inv, inv_smul_eq_iff, eq_comm, UpperHalfPlane.ext_iff,
      modular_S_smul, modular_T_smul, UpperHalfPlane.coe_mk, coe_vadd,
      ← mul_one (_ : ℂ)⁻¹, inv_mul_eq_iff_eq_mul₀ (neg_ne_zero.mpr ρ.ne_zero)]
    grind [ρ_sq, ofReal_one]
  rw [hgeq, hρ, mul_assoc, mul_smul, hSTρ] at hg
  suffices g 0 0 = 0 ∨ g 0 0 = 1 by rcases this with h | h <;> simp [h]
  have hgzre := hg.2
  simp only [Fin.isValue, ρ, neg_div, one_div, ← coe_re, coe_T_zpow_smul_eq, add_re, intCast_re,
    abs_le, le_add_iff_nonneg_right, Int.cast_nonneg_iff, neg_add_le_iff_le_add,
    show (2⁻¹ : ℝ) + 2⁻¹ = 1 by norm_num] at hgzre
  rw [← Int.cast_one (R := ℝ), Int.cast_le] at hgzre
  grind
/-
**ModularGroup.case_c_one_d_neg_one** 是 Mathlib 中的一个引理，位于命名空间 `ModularGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma case_c_one_d_neg_one (hz : z ∈ 𝒟) (hg : g • z ∈ 𝒟) (hg' : ‖denom g z‖ ≤ 1)
    (hc : g 1 0 = 1) (hd : g 1 1 = -1) :
    (g = S * T⁻¹ ∨ g = T⁻¹ * S * T⁻¹) ∧ z = (1 : ℝ) +ᵥ ρ := by
  have : g 0 1 = -g 0 0 - 1 := by
    have := g.property
    simp_rw [det_fin_two] at this
    grind
  have hgeq : g = T ^ g 0 0 * S * T⁻¹ := by
    refine Subtype.ext ?_
    rw [coe_mul, coe_mul, coe_T_zpow, coe_S, ← zpow_neg_one, coe_T_zpow, mul_fin_two, mul_fin_two]
    ring_nf
    ext i j
    fin_cases i <;> fin_cases j <;> [tauto; skip; tauto; tauto]
    simp [this]
    ring_nf
  have hnorm : ‖(z : ℂ) - 1‖ ≤ 1 := by
    convert! hg' using 2
    simp [denom, hc, hd, sub_eq_add_neg]
  rw [norm_def, Real.sqrt_le_one] at hnorm
  have : normSq (z - 1) = normSq z + (-2 * z.re + 1) := by
    simp [normSq]
    ring
  rw [this] at hnorm
  obtain ⟨h, h'⟩ : normSq z = 1 ∧ z.re = 1 / 2 := by
    have : 1 ≤ normSq z := hz.1
    have : 0 ≤ -2 * z.re + 1 := by linarith [(le_abs_self _).trans hz.2]
    constructor <;> linarith
  have hρ : z = (1 : ℝ) +ᵥ ρ := by
    apply eq_of_re_of_norm
    · norm_num [h', ρ]
    · rw [norm_def, h, coe_vadd, ofReal_one,
        show 1 + (ρ : ℂ) = -ρ ^ 2 by grind [ρ_sq], norm_neg, norm_pow, norm_ρ, Real.sqrt_one,
        one_pow]
  refine ⟨?_, hρ⟩
  rw [hgeq, hρ, mul_assoc, mul_smul] at hg
  have : S • ρ = T • ρ := by
    rw [UpperHalfPlane.ext_iff, modular_S_smul, modular_T_smul, UpperHalfPlane.coe_mk,
      coe_vadd, ← mul_one (_ : ℂ)⁻¹, inv_mul_eq_iff_eq_mul₀ (neg_ne_zero.mpr ρ.ne_zero)]
    grind [ρ_sq, ofReal_one]
  have : (S * T⁻¹) • ((1 : ℝ) +ᵥ ρ) = (1 : ℝ) +ᵥ ρ := by
    rw [mul_smul, ← SL_neg_smul S, ← S_inv, inv_smul_eq_iff, ← zpow_neg_one,
    modular_T_zpow_smul, Int.cast_neg, Int.cast_one, neg_vadd_vadd,
    ← inv_smul_eq_iff, S_inv, SL_neg_smul, this, modular_T_smul]
  rw [this] at hg
  rw [hgeq]
  suffices g 0 0 = 0 ∨ g 0 0 = -1 by rcases this with h | h <;> simp [h]
  have : (-1 : ℝ) ≤ g 0 0 ∧ g 0 0 ≤ 0 := by
    simpa only [ρ, neg_div, one_div, ← coe_re, coe_T_zpow_smul_eq, coe_vadd, add_re, ofReal_re,
      show 1 + (-2⁻¹ : ℝ) = 2⁻¹ by norm_num, intCast_re, abs_le, ← sub_le_iff_le_add',
      show (-2⁻¹ : ℝ) - (2⁻¹ : ℝ) = -1 by norm_num, add_le_iff_nonpos_right, Int.cast_nonpos] using
      hg.2
  rw [← Int.cast_one, ← Int.cast_neg, Int.cast_le] at this
  grind

set_option backward.isDefEq.respectTransparency false in
/-
**ModularGroup.serreTheorem_im_eq** 是 Mathlib 中的一个引理，位于命名空间 `ModularGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma serreTheorem_im_eq (hz : z ∈ 𝒟) (hg : g • z ∈ 𝒟) : (g • z).im = z.im := by
  wlog hden : z.im ≤ (g • z).im
  · rw [← this (g := g⁻¹) hg (by simpa using hz) (by simpa using le_of_not_ge hden)]
    simp
  wlog hc : 0 ≤ g 1 0
  · -- TODO: `wlog` leaves junk copies of variables in scope
    simpa using @this (-g) z (-g) z hz (by simpa using hg)
      (by simpa using hden) (by simpa using (not_le.mp hc).le)
  rw [im_smul_eq_div_normSq, le_div_iff₀ (normSq_denom_pos _ z.im_ne_zero),
    mul_le_iff_le_one_right z.im_pos, normSq_eq_norm_sq, sq_le_one_iff₀ (norm_nonneg _)] at hden
  have hc : g 1 0 = 0 ∨ g 1 0 = 1 := by grind [abs_c_le_one hz hg]
  rcases hc with hc | hc
  · rcases cases_c_zero hz hg hc with h | h | h | h <;>
    rcases h with ⟨(rfl | rfl), -⟩ <;>
    simp only [← zpow_neg_one, im_T_zpow_smul, im_T_smul, one_smul, SL_neg_smul]
  · rw [im_smul_eq_div_normSq, div_eq_iff (normSq_denom_pos _ z.im_ne_zero).ne',
    eq_comm, mul_eq_left₀ z.im_ne_zero]
    rcases Int.abs_le_one_iff.mp (cases_d_of_c_eq_one hz hden hc) with hd | hd | hd
    · rcases cases_c_one_d_zero hz hg hden hc hd with
        ⟨rfl, hnm⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp [normSq_eq_norm_sq, denom, coe_S, hnm]
      · rw [show T⁻¹ * S = ⟨!![-1, -1; 1, 0], by simp⟩ by decide]
        norm_num [ρ, denom, ← pow_two, div_pow]
      · rw [show T * S = ⟨!![1, -1; 1, 0], by simp⟩ by decide]
        norm_num [ρ, denom, normSq, ← pow_two, div_pow]
    · rcases case_c_one_d_one hz hg hden hc hd with ⟨(rfl | rfl), rfl⟩
      · rw [show S * T = ⟨!![0, -1; 1, 1], by simp⟩ by decide]
        norm_num [ρ, denom, normSq, ← pow_two, div_pow]
      · rw [show T * S * T = ⟨!![1, 0; 1, 1], by simp⟩ by decide]
        norm_num [ρ, denom, normSq, ← pow_two, div_pow]
    · rcases case_c_one_d_neg_one hz hg hden hc hd with ⟨(rfl | rfl), rfl⟩
      · rw [show S * T⁻¹ = ⟨!![0, -1; 1, -1], by simp⟩ by decide]
        norm_num [ρ, denom, normSq, ← pow_two, div_pow]
      · rw [show T⁻¹ * S * T⁻¹ = ⟨!![-1, 0; 1, -1], by simp⟩ by decide]
        norm_num [ρ, denom, normSq, ← pow_two, div_pow]

/-- Classify the `z` and `g` with `z ∈ 𝒟` and `g • z ∈ 𝒟`. -/
/-
**ModularGroup.cases_of_mem_fd_smul_mem_fd** 是 Mathlib 中的一个引理，位于命名空间 `ModularGro
up`。
形式化陈述：cases_of_mem_fd_smul_mem_fd (hz : z in 𝒟) (hg : g • z in 𝒟) : (g = 1 ∨ g =
 -1) ∨ ((g = T ∨ g = -T) ∧ z.re = -1 / 2) ∨ ((g = T⁻¹ ∨ g = -T⁻¹) ∧ z.re = 1 / 2
) ∨ ((g = S ∨ g = -S) ∧ ‖(z : Complex)‖ = 1) ∨ ((g = T * S ∨ g = -(T * S)) ∧ z =
 (1 : Real) +ᵥ ρ) ∨ ((g = T⁻¹ * S * T⁻¹ ∨ g = -(T⁻¹ * S * T⁻¹)) ∧ z = (1 : Real)
 +ᵥ ρ) ∨ ((g = S * T⁻¹ ∨ g = -(S * T⁻¹)) ∧ z = (1 : Real) +ᵥ ρ) ∨ ((g = S * T ∨ 
g = -(S * T)) ∧ z = ρ) ∨ ((g = T * S * T ∨ g = -(T * S * T)) ∧ z = ρ) ∨ ((g = T⁻
¹ * S ∨ g = -(T⁻¹ * S)) ∧ 
参数：hz : z in 𝒟；hg : g • z in 𝒟。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.NumberTheory.Modular.0.ModularGroup.serreTheorem_im_eq`
：∀ {g : Matrix.SpecialLinearGroup (Fin 2) ℤ} {z : UpperHalfPlane},   z ∈ Modular
Group.fd → g • z ∈ ModularGroup.fd → (g • z).im = z.im
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Int.abs_le_one_iff`：abs_le_one_iff {a : Int} : |a| <= 1 ↔ a = 0 ∨ a = 1 
∨ a = -1
· 使用定理 `_private.Mathlib.NumberTheory.Modular.0.ModularGroup.cases_d_of_c_eq_one
`：∀ {g : Matrix.SpecialLinearGroup (Fin 2) ℤ} {z : UpperHalfPlane},   z ∈ Modula
rGroup.fd →     ‖UpperHalfPlane.denom (Matrix.SpecialLinearGro…
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_eq_one_iff_of_nonneg`：pow_eq_one_iff_of_nonneg (ha : 0 <= a) (hn : n
 != 0) : a ^ n = 1 ↔ a = 1
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用引理 `Complex.normSq_eq_norm_sq`：normSq_eq_norm_sq (z : Complex) : normSq z = 
‖z‖ ^ 2
· 使用定理 `mul_eq_left₀`：mul_eq_left₀ [IsLeftCancelMulZero M₀] (ha : a != 0) : a * 
b = a ↔ b = 1
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `UpperHalfPlane.im_ne_zero`：im_ne_zero (z : ℍ) : z.im != 0
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用引理 `div_eq_iff`：div_eq_iff (hb : b != 0) : a / b = c ↔ a = c * b
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `UpperHalfPlane.normSq_denom_pos`：normSq_denom_pos (g : GL (Fin 2) Real) 
{z : Complex} (hz : z.im != 0) : 0 < Complex.normSq (denom g z)
· 使用定理 `ModularGroup.im_smul_eq_div_normSq`：im_smul_eq_div_normSq : (g • z).im =
 z.im / Complex.normSq (denom g z)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ModularGroup.SL_neg_smul`：SL_neg_smul : -g • z = g • z
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
Classify the `z` and `g` with `z ∈ 𝒟` and `g • z ∈ 𝒟`.
-/
lemma cases_of_mem_fd_smul_mem_fd (hz : z ∈ 𝒟) (hg : g • z ∈ 𝒟) :
    (g = 1 ∨ g = -1) ∨
    ((g = T ∨ g = -T) ∧ z.re = -1 / 2) ∨
    ((g = T⁻¹ ∨ g = -T⁻¹) ∧ z.re = 1 / 2) ∨
    ((g = S ∨ g = -S) ∧ ‖(z : ℂ)‖ = 1) ∨
    ((g = T * S ∨ g = -(T * S)) ∧ z = (1 : ℝ) +ᵥ ρ) ∨
    ((g = T⁻¹ * S * T⁻¹ ∨ g = -(T⁻¹ * S * T⁻¹)) ∧ z = (1 : ℝ) +ᵥ ρ) ∨
    ((g = S * T⁻¹ ∨ g = -(S * T⁻¹)) ∧ z = (1 : ℝ) +ᵥ ρ) ∨
    ((g = S * T ∨ g = -(S * T)) ∧ z = ρ) ∨
    ((g = T * S * T ∨ g = -(T * S * T)) ∧ z = ρ) ∨
    ((g = T⁻¹ * S ∨ g = -(T⁻¹ * S)) ∧ z = ρ) := by
  have him : (g • z).im = z.im := serreTheorem_im_eq hz hg
  wlog hc : 0 ≤ g 1 0
  · simpa [neg_eq_iff_eq_neg, or_comm] using @this (-g) z hz (by simpa using hg)
      (by simpa using him) (by simpa using (not_le.mp hc).le)
  rw [im_smul_eq_div_normSq, div_eq_iff (normSq_denom_pos _ z.im_ne_zero).ne',
    eq_comm, mul_eq_left₀ z.im_ne_zero, normSq_eq_norm_sq,
    pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero] at him
  have hc : g 1 0 = 0 ∨ g 1 0 = 1 := by grind [abs_c_le_one hz hg]
  rcases hc with hc | hc
  · grind [cases_c_zero hz hg hc] -- ± T, T⁻¹
  · rcases Int.abs_le_one_iff.mp (cases_d_of_c_eq_one hz him.le hc) with hd | hd | hd
    · grind [cases_c_one_d_zero hz hg him.le hc hd] -- ± S, T⁻¹S, TS
    · grind [case_c_one_d_one hz hg him.le hc hd] -- ± ST, TST
    · grind [case_c_one_d_neg_one hz hg him.le hc hd] -- ± ST⁻¹, T⁻¹ST⁻¹

/-- If `z ∈ 𝒟` and `z ≠ I, ρ, 1 + ρ`, then the stabilizer of `z` in `SL(2, ℤ)` is `± 1`. -/
/-
**ModularGroup.stabilizer_of_ne** 是 Mathlib 中的一个引理，位于命名空间 `ModularGroup`。
形式化陈述：stabilizer_of_ne (hz : z in 𝒟) (hg : g • z = z) (hzI : z != I) (hzρ : z !=
 ρ) (hzρ' : z != (1 : Real) +ᵥ ρ) : g = 1 ∨ g = -1
参数：hz : z in 𝒟；hg : g • z = z；hzI : z != I；hzρ : z != ρ；hzρ' : z != (1 : Real) +
ᵥ ρ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ModularGroup.re_T_smul`：re_T_smul : (T • z).re = z.re + 1
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `inv_smul_eq_iff`：∀ {G : Type u_3} {α : Type u_5} [inst : Group G] [inst_
1 : MulAction G α] {g : G} {a b : α}, g⁻¹ • a = b ↔ a = g • b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `UpperHalfPlane.ext_iff`：∀ {x y : UpperHalfPlane}, x = y ↔ ↑x = ↑y
· 使用引理 `UpperHalfPlane.coe_I`：coe_I : I = Complex.I
· 使用引理 `sq_eq_sq_iff_eq_or_eq_neg`：sq_eq_sq_iff_eq_or_eq_neg : a ^ 2 = b ^ 2 ↔ a
 = b ∨ a = -b
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Complex.I_sq`：I_sq : I ^ 2 = -1
· 使用定理 `neg_eq_iff_eq_neg`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, 
-a = b ↔ a = -b
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用引理 `inv_mul_eq_iff_eq_mul₀`：inv_mul_eq_iff_eq_mul₀ (ha : a != 0) : a⁻¹ * b =
 c ↔ b = a * c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_ne_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a ≠
 0 ↔ a ≠ 0
· 使用定理 `UpperHalfPlane.ne_zero`：ne_zero (z : ℍ) : (z : Complex) != 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `UpperHalfPlane.im_inv_neg_coe_pos`：im_inv_neg_coe_pos (z : ℍ) : 0 < (-z 
: Complex)⁻¹.im
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
If `z ∈ 𝒟` and `z ≠ I, ρ, 1 + ρ`, then the stabilizer of `z` in `SL(2, ℤ)` is `±
 1`.
-/
lemma stabilizer_of_ne (hz : z ∈ 𝒟) (hg : g • z = z)
    (hzI : z ≠ I) (hzρ : z ≠ ρ) (hzρ' : z ≠ (1 : ℝ) +ᵥ ρ) :
    g = 1 ∨ g = -1 := by
  have : T • z ≠ z := by
    apply_fun UpperHalfPlane.re
    simp [-sl_moeb, re_T_smul]
  have : T⁻¹ • z ≠ z := by rwa [ne_eq, inv_smul_eq_iff, eq_comm]
  have : (z : ℂ) ≠ -I := by grind [neg_im, coe_I, Complex.I_im, z.coe_im_pos]
  have : S • z ≠ z := by
    contrapose hzI
    rw [UpperHalfPlane.ext_iff, modular_S_smul, coe_mk, ← mul_one (_ : ℂ)⁻¹,
      inv_mul_eq_iff_eq_mul₀ (neg_ne_zero.mpr z.ne_zero), neg_mul, ← neg_eq_iff_eq_neg, ← I_sq,
      ← sq, sq_eq_sq_iff_eq_or_eq_neg, ← coe_I, ← UpperHalfPlane.ext_iff] at hzI
    grind
  all_goals grind [cases_of_mem_fd_smul_mem_fd hz (hg ▸ hz), SL_neg_smul]
/-
**ModularGroup.stabilizer_I** 是 Mathlib 中的一个引理，位于命名空间 `ModularGroup`。
形式化陈述：stabilizer_I : g • I = I ↔ g in ({1, -1, S, -S} : Finset SL(2, Int))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `ModularGroup.cases_of_mem_fd_smul_mem_fd`：cases_of_mem_fd_smul_mem_fd (h
z : z in 𝒟) (hg : g • z in 𝒟) : (g = 1 ∨ g = -1) ∨ ((g = T ∨ g = -T) ∧ z.re = -1
 / 2) ∨ ((g = T⁻¹ ∨ g = -T⁻¹) …
· 使用引理 `ModularGroup.I_mem_fd`：I_mem_fd : I in 𝒟
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用引理 `UpperHalfPlane.I_re`：I_re : I.re = 0
· 使用定理 `Mathlib.Meta.NormNum.IsRat.neg_to_eq`：∀ {α : Type u_1} [inst : DivisionR
ing α] {n d : ℕ} {a n' d' : α},   Mathlib.Meta.NormNum.IsRat a (Int.negOfNat n) 
d → ↑n = n' → ↑d = d' → a …
· 使用定理 `Mathlib.Meta.NormNum.isRat_div`：∀ {α : Type u} [inst : DivisionRing α] {
a b : α} {cn : ℤ} {cd : ℕ},   Mathlib.Meta.NormNum.IsRat (a * b⁻¹) cn cd → Mathl
ib.Meta.NormNum.IsRa…
· 使用定理 `Mathlib.Meta.NormNum.isRat_mul`：isRat_mul {α} [Ring α] {f : α -> α -> α}
 {a b : α} {na nb nc : Int} {da db dc k : Nat} : f = HMul.hMul -> IsRat a na da 
-> IsRat b nb db -> …
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isRat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℤ}, Mathlib.Meta.NormNum.IsInt a n → Mathlib.Meta.NormNum.IsRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isRat`：∀ {α : Type u_1} [inst : Ring α] 
{a : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n d → Mathlib.Meta.NormNum.I
sRat a (Int.ofNat n) d
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_eq_false`：∀ {α : Type u_1} [inst : Semiring
 α] [CharZero α] {a b : α} {na nb da db : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n
a da →     Mathlib.Meta.Nor…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false`：¬False
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_eq`：∀ {α : Type u_1} [inst : DivisionSem
iring α] {n d : ℕ} {a n' d' : α},   Mathlib.Meta.NormNum.IsNNRat a n d → ↑n = n'
 → ↑d = d' → a = n' / d'
（共 57 条，此处仅展示前 30 条）
-/
lemma stabilizer_I : g • I = I ↔ g ∈ ({1, -1, S, -S} : Finset SL(2, ℤ)) := by
  constructor
  · intro hg
    have := cases_of_mem_fd_smul_mem_fd I_mem_fd (hg.symm ▸ I_mem_fd)
    norm_num [UpperHalfPlane.ext_iff, Complex.ext_iff, ρ] at this
    grind
  · suffices S • I = I by simp +contextual [-sl_moeb, or_imp, this]
    rw [modular_S_smul, UpperHalfPlane.ext_iff]
    norm_num
/-
**ModularGroup.stabilizer_** 是 Mathlib 中的一个引理，位于命名空间 `ModularGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma stabilizer_ρ :
    g • ρ = ρ ↔ g ∈ ({1, -1, S * T, -(S * T), T⁻¹ * S, -(T⁻¹ * S)} : Finset SL(2, ℤ)) := by
  constructor
  · intro hg
    have neS : g ≠ S ∧ g ≠ -S := by
      have : S • ρ ≠ ρ := by
        rw [ne_eq, UpperHalfPlane.ext_iff, modular_S_smul, coe_mk, Complex.ext_iff]
        norm_num [ρ, ← pow_two, div_pow]
      grind [SL_neg_smul]
    have neT : g ≠ T ∧ g ≠ -T ∧ g ≠ T⁻¹ ∧ g ≠ -T⁻¹ := by
      have : T • ρ ≠ ρ := by
        rw [ne_eq, UpperHalfPlane.ext_iff, modular_T_smul, coe_vadd]
        norm_num
      have : T⁻¹ • ρ ≠ ρ := by rwa [ne_eq, inv_smul_eq_iff, eq_comm]
      grind [SL_neg_smul]
    have neTST : g ≠ T * S * T ∧ g ≠ -(T * S * T) := by
      have : (T * S * T) • ρ ≠ ρ := by
        simp only [mul_smul, modular_T_smul, modular_S_smul,
          ne_eq, UpperHalfPlane.ext_iff, Complex.ext_iff]
        norm_num [ρ, ← pow_two, div_pow, normSq]
      grind [SL_neg_smul]
    have := cases_of_mem_fd_smul_mem_fd ρ_mem_fd (hg ▸ ρ_mem_fd)
    norm_num [UpperHalfPlane.ext_iff, Complex.ext_iff, norm_ρ, ρ, neS, neT, neTST] at this
    grind
  · suffices (S * T) • ρ = ρ ∧ (T⁻¹ * S) • ρ = ρ by simp +contextual [-sl_moeb, or_imp, this]
    rw [mul_smul T⁻¹, inv_smul_eq_iff, ← eq_inv_smul_iff (g := S), S_inv, SL_neg_smul,
      mul_smul, eq_comm, and_self, modular_T_smul, modular_S_smul, UpperHalfPlane.ext_iff]
    norm_num [ρ, Complex.ext_iff, normSq, ← pow_two, div_pow]

/-- Second Fundamental Domain Lemma: if `z ∈ 𝒟ᵒ` and `g • z ∈ 𝒟`, then `g = ± 1`. -/
/-
**ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fd** 是 Mathlib 中的一个定理，位于命名空间 `Mo
dularGroup`。
形式化陈述：eq_one_or_neg_one_of_mem_fdo_mem_fd (hz : z in 𝒟ᵒ) (hg : g • z in 𝒟) : g =
 1 ∨ g = -1
参数：hz : z in 𝒟ᵒ；hg : g • z in 𝒟。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Mathlib.Meta.NormNum.IsRat.neg_to_eq`：∀ {α : Type u_1} [inst : DivisionR
ing α] {n d : ℕ} {a n' d' : α},   Mathlib.Meta.NormNum.IsRat a (Int.negOfNat n) 
d → ↑n = n' → ↑d = d' → a …
· 使用定理 `Mathlib.Meta.NormNum.isRat_div`：∀ {α : Type u} [inst : DivisionRing α] {
a b : α} {cn : ℤ} {cd : ℕ},   Mathlib.Meta.NormNum.IsRat (a * b⁻¹) cn cd → Mathl
ib.Meta.NormNum.IsRa…
· 使用定理 `Mathlib.Meta.NormNum.isRat_mul`：isRat_mul {α} [Ring α] {f : α -> α -> α}
 {a b : α} {na nb nc : Int} {da db dc k : Nat} : f = HMul.hMul -> IsRat a na da 
-> IsRat b nb db -> …
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isRat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℤ}, Mathlib.Meta.NormNum.IsInt a n → Mathlib.Meta.NormNum.IsRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isRat`：∀ {α : Type u_1} [inst : Ring α] 
{a : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n d → Mathlib.Meta.NormNum.I
sRat a (Int.ofNat n) d
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isRat_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {n n' : ℤ} {d : ℕ},   f = Neg.neg → Mathlib.Meta.NormNum.IsRat a n 
d → n.neg = n' → Mat…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `UpperHalfPlane.mk.congr_simp`：∀ (coe coe_1 : ℂ) (e_coe : coe = coe_1) (c
oe_im_pos : 0 < coe.im),   { coe := coe, coe_im_pos := coe_im_pos } = { coe := c
oe_1, coe_im_pos :…
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_eq`：∀ {α : Type u_1} [inst : DivisionSem
iring α] {n d : ℕ} {a n' d' : α},   Mathlib.Meta.NormNum.IsNNRat a n d → ↑n = n'
 → ↑d = d' → a = n' / d'
· 使用定理 `Mathlib.Meta.NormNum.IsRat.to_isNNRat`：∀ {α : Type u_1} [inst : Ring α] 
{a : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsRat a (Int.ofNat n) d → Mathlib.Meta
.NormNum.IsNNRat a n d
· 使用定理 `Mathlib.Meta.NormNum.isRat_add`：isRat_add {α} [Ring α] {f : α -> α -> α}
 {a b : α} {na nb nc : Int} {da db dc k : Nat} : f = HAdd.hAdd -> IsRat a na da 
-> IsRat b nb db -> …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True

--- 原说明 ---
Second Fundamental Domain Lemma: if `z ∈ 𝒟ᵒ` and `g • z ∈ 𝒟`, then `g = ± 1`.
-/
theorem eq_one_or_neg_one_of_mem_fdo_mem_fd (hz : z ∈ 𝒟ᵒ) (hg : g • z ∈ 𝒟) : g = 1 ∨ g = -1 := by
  have : ρ ∉ 𝒟ᵒ := by
    intro h
    grind [norm_ρ, one_lt_normSq_iff.mp h.1]
  have : (1 : ℝ) +ᵥ ρ ∉ 𝒟ᵒ := by
    intro h
    have : ((1 : ℝ) +ᵥ ρ).re = 1 / 2 := by norm_num [← coe_re, coe_vadd, ρ]
    grind [h.2]
  grind [one_lt_normSq_iff, hz.1, hz.2, cases_of_mem_fd_smul_mem_fd (fdo_subset_fd hz) hg]

/-- Second Fundamental Domain Lemma: if both `z` and `g • z` are in the open domain `𝒟ᵒ`,
where `z : ℍ` and `g : SL(2, ℤ)`, then `g = ±1`. -/
/-
**ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fdo** 是 Mathlib 中的一个定理，位于命名空间 `M
odularGroup`。
形式化陈述：eq_one_or_neg_one_of_mem_fdo_mem_fdo (hz : z in 𝒟ᵒ) (hg : g • z in 𝒟ᵒ) : g
 = 1 ∨ g = -1
参数：hz : z in 𝒟ᵒ；hg : g • z in 𝒟ᵒ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fd`：eq_one_or_neg_one_of_m
em_fdo_mem_fd (hz : z in 𝒟ᵒ) (hg : g • z in 𝒟) : g = 1 ∨ g = -1
· 使用引理 `ModularGroup.fdo_subset_fd`：fdo_subset_fd : 𝒟ᵒ subseteq 𝒟

--- 原说明 ---
Second Fundamental Domain Lemma: if both `z` and `g • z` are in the open domain 
`𝒟ᵒ`,
where `z : ℍ` and `g : SL(2, ℤ)`, then `g = ±1`.
-/
theorem eq_one_or_neg_one_of_mem_fdo_mem_fdo (hz : z ∈ 𝒟ᵒ) (hg : g • z ∈ 𝒟ᵒ) : g = 1 ∨ g = -1 :=
  eq_one_or_neg_one_of_mem_fdo_mem_fd hz (fdo_subset_fd hg)

/-- This was previously an auxiliary result en route to
`ModularGroup.eq_smul_self_of_mem_fdo_mem_fdo`. It is now deprecated, since the proof has been
refactored so this step is no longer needed. -/
@[deprecated eq_one_or_neg_one_of_mem_fdo_mem_fdo (since := "2026-03-19")]
/-
**ModularGroup.c_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `ModularGroup`。
形式化陈述：c_eq_zero (hz : z in 𝒟ᵒ) (hg : g • z in 𝒟ᵒ) : g 1 0 = 0
参数：hz : z in 𝒟ᵒ；hg : g • z in 𝒟ᵒ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fdo`：eq_one_or_neg_one_of_
mem_fdo_mem_fdo (hz : z in 𝒟ᵒ) (hg : g • z in 𝒟ᵒ) : g = 1 ∨ g = -1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
This was previously an auxiliary result en route to
`ModularGroup.eq_smul_self_of_mem_fdo_mem_fdo`. It is now deprecated, since the 
proof has been
refactored so this step is no longer needed.
-/
theorem c_eq_zero (hz : z ∈ 𝒟ᵒ) (hg : g • z ∈ 𝒟ᵒ) : g 1 0 = 0 := by
  rcases eq_one_or_neg_one_of_mem_fdo_mem_fdo hz hg with rfl | rfl <;> rfl

/-- Second Fundamental Domain Lemma: if both `z` and `g • z` are in the open domain `𝒟ᵒ`,
where `z : ℍ` and `g : SL(2, ℤ)`, then `z = g • z`. -/
/-
**ModularGroup.eq_smul_self_of_mem_fdo_mem_fdo** 是 Mathlib 中的一个定理，位于命名空间 `Modula
rGroup`。
形式化陈述：eq_smul_self_of_mem_fdo_mem_fdo (hz : z in 𝒟ᵒ) (hg : g • z in 𝒟ᵒ) : z = g 
• z
参数：hz : z in 𝒟ᵒ；hg : g • z in 𝒟ᵒ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fdo`：eq_one_or_neg_one_of_
mem_fdo_mem_fdo (hz : z in 𝒟ᵒ) (hg : g • z in 𝒟ᵒ) : g = 1 ∨ g = -1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ModularGroup.SL_neg_smul`：SL_neg_smul : -g • z = g • z

--- 原说明 ---
Second Fundamental Domain Lemma: if both `z` and `g • z` are in the open domain 
`𝒟ᵒ`,
where `z : ℍ` and `g : SL(2, ℤ)`, then `z = g • z`.
-/
theorem eq_smul_self_of_mem_fdo_mem_fdo (hz : z ∈ 𝒟ᵒ) (hg : g • z ∈ 𝒟ᵒ) : z = g • z := by
  rcases eq_one_or_neg_one_of_mem_fdo_mem_fdo hz hg with rfl | rfl <;> simp

end UniqueRepresentative

section Topology
/-!
## Topological properties of the fundamental domain
-/

/-
**ModularGroup.isClosed_fd** 是 Mathlib 中的一个引理，位于命名空间 `ModularGroup`。
形式化陈述：isClosed_fd : IsClosed 𝒟
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.inter`：IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : I
sClosed (s₁ inter s₂)
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `Complex.continuous_normSq`：Continuous ⇑Complex.normSq
· 使用定理 `UpperHalfPlane.continuous_coe`：continuous_coe : Continuous ((↑) : ℍ -> C
omplex)
· 使用定理 `isClosed_Ici`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Preor
der α] [ClosedIciTopology α] {a : α}, IsClosed (Set.Ici a)
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `isClosed_le`：isClosed_le [TopologicalSpace β] {f g : β -> α} (hf : Conti
nuous f) (hg : Continuous g) : IsClosed { b | f b <= g b }
· 使用定理 `Continuous.abs`：∀ {G : Type u_1} [inst : TopologicalSpace G] [inst_1 : A
ddCommGroup G] [inst_2 : LinearOrder G] [IsOrderedAddMonoid G]   [OrderTopology 
G] {…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `UpperHalfPlane.continuous_re`：continuous_re : Continuous re
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)

--- 原说明 ---
## Topological properties of the fundamental domain
-/
lemma isClosed_fd : IsClosed 𝒟 := by
  refine .inter (.preimage (by fun_prop) isClosed_Ici) ?_
  exact isClosed_le (f := fun z : ℍ ↦ |z.re|) (by fun_prop) continuous_const
/-
**ModularGroup.isOpen_fdo** 是 Mathlib 中的一个引理，位于命名空间 `ModularGroup`。
形式化陈述：isOpen_fdo : IsOpen 𝒟ᵒ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `Complex.continuous_normSq`：Continuous ⇑Complex.normSq
· 使用定理 `UpperHalfPlane.continuous_coe`：continuous_coe : Continuous ((↑) : ℍ -> C
omplex)
· 使用定理 `isOpen_Ioi`：isOpen_Ioi : IsOpen (Ioi a)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `isOpen_lt`：isOpen_lt [TopologicalSpace β] {f g : β -> α} (hf : Continuou
s f) (hg : Continuous g) : IsOpen { b | f b < g b }
· 使用定理 `Continuous.abs`：∀ {G : Type u_1} [inst : TopologicalSpace G] [inst_1 : A
ddCommGroup G] [inst_2 : LinearOrder G] [IsOrderedAddMonoid G]   [OrderTopology 
G] {…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `UpperHalfPlane.continuous_re`：continuous_re : Continuous re
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
-/
lemma isOpen_fdo : IsOpen 𝒟ᵒ := by
  refine .inter (.preimage (by fun_prop) isOpen_Ioi) ?_
  exact isOpen_lt (f := fun z : ℍ ↦ |z.re|) (by fun_prop) continuous_const

/-- Explicit formula for the image of `ModularGroup.fdo` in `ℂ`. -/
/-
**ModularGroup.coe_fdo** 是 Mathlib 中的一个引理，位于命名空间 `ModularGroup`。
形式化陈述：coe_fdo : (↑) '' 𝒟ᵒ = {z : Complex | 0 < z.im ∧ 1 < ‖z‖ ∧ |z.re| < 1/2}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Complex.one_lt_normSq_iff`：one_lt_normSq_iff {x : Complex} : 1 < normSq 
x ↔ 1 < ‖x‖
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
Explicit formula for the image of `ModularGroup.fdo` in `ℂ`.
-/
lemma coe_fdo : (↑) '' 𝒟ᵒ = {z : ℂ | 0 < z.im ∧ 1 < ‖z‖ ∧ |z.re| < 1/2} := by
  ext x
  refine ⟨?_, fun ⟨hxim, hxnorm, hxre⟩ ↦ ⟨⟨x, hxim⟩, ⟨one_lt_normSq_iff.mpr hxnorm, hxre⟩, rfl⟩⟩
  rintro ⟨τ, hτ, rfl⟩
  exact ⟨τ.im_pos, one_lt_normSq_iff.mp hτ.1, hτ.2⟩

/-- Explicit formula for the image of `ModularGroup.fd` in `ℂ`. -/
/-
**ModularGroup.coe_fd** 是 Mathlib 中的一个引理，位于命名空间 `ModularGroup`。
形式化陈述：coe_fd : (↑) '' 𝒟 = {z : Complex | 0 < z.im ∧ 1 <= ‖z‖ ∧ |z.re| <= 1/2}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Complex.one_le_normSq_iff`：one_le_normSq_iff {x : Complex} : 1 <= normSq
 x ↔ 1 <= ‖x‖
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
Explicit formula for the image of `ModularGroup.fd` in `ℂ`.
-/
lemma coe_fd : (↑) '' 𝒟 = {z : ℂ | 0 < z.im ∧ 1 ≤ ‖z‖ ∧ |z.re| ≤ 1/2} := by
  ext x
  refine ⟨?_, fun ⟨hxim, hxnorm, hxre⟩ ↦ ⟨⟨x, hxim⟩, ⟨one_le_normSq_iff.mpr hxnorm, hxre⟩, rfl⟩⟩
  rintro ⟨τ, hτ, rfl⟩
  exact ⟨τ.im_pos, one_le_normSq_iff.mp hτ.1, hτ.2⟩

/--
The image of the fundamental domain `𝒟` in `ℂ` is closed.
This is not immediate (unlike the analogous statement for `𝒟ᵒ`),
since the inclusion of `ℍ` in `ℂ` is an open but not a closed map.
-/
/-
**ModularGroup.isClosed_coe_fd** 是 Mathlib 中的一个引理，位于命名空间 `ModularGroup`。
形式化陈述：isClosed_coe_fd : IsClosed ((↑) '' 𝒟 : Set Complex)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ModularGroup.coe_fd`：coe_fd : (↑) '' 𝒟 = {z : Complex | 0 < z.im ∧ 1 <= 
‖z‖ ∧ |z.re| <= 1/2}
· 使用定理 `IsClosed.inter`：IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : I
sClosed (s₁ inter s₂)
· 使用定理 `isClosed_le`：isClosed_le [TopologicalSpace β] {f g : β -> α} (hf : Conti
nuous f) (hg : Continuous g) : IsClosed { b | f b <= g b }
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `Complex.continuous_im`：Continuous Complex.im
· 使用定理 `continuous_norm`：∀ {E : Type u_4} [inst : SeminormedAddGroup E], Continu
ous fun a => ‖a‖
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_abs`：∀ {G : Type u_1} [inst : TopologicalSpace G] [inst_1 : A
ddCommGroup G] [inst_2 : LinearOrder G] [IsOrderedAddMonoid G]   [OrderTopology 
G], …
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Complex.continuous_re`：Continuous Complex.re
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LE.le.lt_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a

--- 原说明 ---
The image of the fundamental domain `𝒟` in `ℂ` is closed.
This is not immediate (unlike the analogous statement for `𝒟ᵒ`),
since the inclusion of `ℍ` in `ℂ` is an open but not a closed map.
-/
lemma isClosed_coe_fd : IsClosed ((↑) '' 𝒟 : Set ℂ) := by
  rw [coe_fd]
  have : IsClosed {z : ℂ | 0 ≤ z.im ∧ 1 ≤ ‖z‖ ∧ |z.re| ≤ 1/2} := by
    refine .inter ?_ (.inter ?_ ?_)
    · exact isClosed_le continuous_const Complex.continuous_im
    · exact isClosed_le continuous_const continuous_norm
    · exact isClosed_le (continuous_abs.comp Complex.continuous_re) continuous_const
  convert! this using 1
  ext x
  refine ⟨fun ⟨him, hre, hnorm⟩ ↦ ⟨him.le, hre, hnorm⟩, fun ⟨him, hre, hnorm⟩ ↦ ⟨?_, hre, hnorm⟩⟩
  exact him.lt_of_ne' <| by grind [abs_re_eq_norm]

/--
The points on the fundamental domain that aren't on the bottom "arc"
are in the closure of the open fundamental domain.
-/
/-
**ModularGroup.mem_closure_of_one_lt_norm** 是 Mathlib 中的一个引理，位于命名空间 `ModularGrou
p`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The points on the fundamental domain that aren't on the bottom "arc"
are in the closure of the open fundamental domain.
-/
private lemma mem_closure_of_one_lt_norm {x : ℍ} (hxnorm : 1 < ‖(x : ℂ)‖) (hxre : |x.re| ≤ 1 / 2) :
    x ∈ closure 𝒟ᵒ := by
  -- Need to show that any `x` in this set is a limit of points in `𝒟ᵒ`.
  -- Idea is to use a line segment through the origin and `x`, and show that points
  -- a little below `x` are in `𝒟ᵒ`. There are some annoyances due
  -- to subtypes, etc.
  apply mem_closure_of_frequently_of_tendsto (α := ℝ)
      (b := 𝓝[<] 1) (f := fun t ↦ ofComplex (t * x))
  · apply Filter.Eventually.frequently
    simp only [fdo, Set.mem_ofPred, Filter.eventually_and, one_lt_normSq_iff]
    refine ⟨Filter.Tendsto.eventually_const_lt hxnorm (.mono_left ?_ nhdsWithin_le_nhds), ?_⟩
    · have : ContinuousAt (fun a : ℝ ↦ (ofComplex (a * x : ℂ) : ℂ)) 1 := by
        refine .comp (by fun_prop) ((OpenPartialHomeomorph.continuousAt _ ?_).comp (by fun_prop))
        simpa [ofComplex] using x.coe_im_pos
      simpa [ofComplex_apply_of_im_pos x.coe_im_pos] using this.tendsto.norm
    · simp only [eventually_nhdsWithin_iff]
      filter_upwards [eventually_gt_nhds zero_lt_one] with a ha ha'
      rw [← coe_re, ofComplex_apply_of_im_pos (by simpa using mul_pos ha x.coe_im_pos)]
      suffices a * |x.re| < 1 / 2 by simpa [abs_of_pos ha]
      nlinarith [Set.mem_Iio.mp ha']
  · refine .mono_left ?_ nhdsWithin_le_nhds
    rw [isOpenEmbedding_coe.tendsto_nhds_iff, Function.comp_def]
    have : Filter.Tendsto (fun t : ℝ ↦ t * (x : ℂ)) (𝓝 1) (𝓝 (x : ℂ)) := by
      rw [show 𝓝 (x : ℂ) = 𝓝 ((1 : ℝ) * (x : ℂ)) by simp]
      exact Continuous.tendsto (by fun_prop) _
    refine this.congr' ?_
    filter_upwards [eventually_gt_nhds zero_lt_one] with a ha
    rw [ofComplex_apply_of_im_pos (by simpa using mul_pos ha x.coe_im_pos)]

open scoped NNReal in
/-- The points on the bottom "arc" of the fundamental domain are in the closure
of the open fundamental domain. -/
/-
**ModularGroup.mem_closure_of_arc** 是 Mathlib 中的一个引理，位于命名空间 `ModularGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The points on the bottom "arc" of the fundamental domain are in the closure
of the open fundamental domain.
-/
private lemma mem_closure_of_arc {x : ℍ} (hxnorm : ‖(x : ℂ)‖ = 1) (hxre : |x.re| ≤ 1 / 2) :
    x ∈ closure 𝒟ᵒ := by
  -- We show that `x` is a limit of points known to be in the closure.
  rw [← closure_closure]
  -- Consider a vertical line going upwards from `x` (parametrized by `ℝ≥0`)
  apply mem_closure_of_frequently_of_tendsto (b := 𝓝[>] 0)
    (f := fun t : ℝ≥0 ↦ ⟨x + t * Complex.I, by
      simpa using! add_pos_of_pos_of_nonneg x.coe_im_pos t.property⟩)
  · apply Filter.Eventually.frequently
    filter_upwards [self_mem_nhdsWithin] with a (ha : 0 < a)
    refine mem_closure_of_one_lt_norm ?_ (by simpa using! hxre)
    suffices 1 < ‖(x : ℂ)‖ ^ 2 + a ^ 2 + 2 * a * x.im by
      rw [← one_lt_normSq_iff]
      convert! this
      simp [← normSq_eq_norm_sq, normSq_apply]
      ring
    rw [hxnorm, one_pow, add_assoc, lt_add_iff_pos_right]
    positivity
  · refine .mono_left ?_ nhdsWithin_le_nhds
    simpa [show 𝓝 (x : ℂ) = 𝓝 (x + (((0 : ℝ≥0) : ℝ) : ℂ) * Complex.I) by simp,
      isOpenEmbedding_coe.tendsto_nhds_iff] using! Continuous.tendsto (by fun_prop) _
/-
**ModularGroup.fd_eq_closure_fdo** 是 Mathlib 中的一个引理，位于命名空间 `ModularGroup`。
形式化陈述：fd_eq_closure_fdo : 𝒟 = closure 𝒟ᵒ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用引理 `lt_or_eq_of_le`：lt_or_eq_of_le : a <= b -> a < b ∨ a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Complex.one_le_normSq_iff`：one_le_normSq_iff {x : Complex} : 1 <= normSq
 x ↔ 1 <= ‖x‖
· 使用定理 `_private.Mathlib.NumberTheory.Modular.0.ModularGroup.mem_closure_of_one_
lt_norm`：∀ {x : UpperHalfPlane}, 1 < ‖↑x‖ → |x.re| ≤ 1 / 2 → x ∈ closure Modular
Group.fdo
· 使用定理 `_private.Mathlib.NumberTheory.Modular.0.ModularGroup.mem_closure_of_arc`
：∀ {x : UpperHalfPlane}, ‖↑x‖ = 1 → |x.re| ≤ 1 / 2 → x ∈ closure ModularGroup.fd
o
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsClosed.closure_subset_iff`：IsClosed.closure_subset_iff (h₁ : IsClosed 
t) : closure s subseteq t ↔ s subseteq t
· 使用引理 `ModularGroup.isClosed_fd`：isClosed_fd : IsClosed 𝒟
· 使用引理 `ModularGroup.fdo_subset_fd`：fdo_subset_fd : 𝒟ᵒ subseteq 𝒟
-/
lemma fd_eq_closure_fdo : 𝒟 = closure 𝒟ᵒ := by
  refine subset_antisymm ?_ (isClosed_fd.closure_subset_iff.mpr fdo_subset_fd)
  intro x ⟨hx, hx'⟩
  rw [one_le_normSq_iff] at hx
  rcases lt_or_eq_of_le hx with hx | hx
  · exact mem_closure_of_one_lt_norm hx hx'
  · exact mem_closure_of_arc hx.symm hx'
/-
**ModularGroup.fdo_eq_interior_fd** 是 Mathlib 中的一个引理，位于命名空间 `ModularGroup`。
形式化陈述：fdo_eq_interior_fd : 𝒟ᵒ = interior 𝒟
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsOpen.subset_interior_iff`：IsOpen.subset_interior_iff (h₁ : IsOpen s) :
 s subseteq interior t ↔ s subseteq t
· 使用引理 `ModularGroup.isOpen_fdo`：isOpen_fdo : IsOpen 𝒟ᵒ
· 使用引理 `ModularGroup.fdo_subset_fd`：fdo_subset_fd : 𝒟ᵒ subseteq 𝒟
· 使用定理 `IsOpenMap.image_interior_subset`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f → 
∀ (s : Set X), f '' i…
· 使用引理 `UpperHalfPlane.isOpenMap_re`：isOpenMap_re : IsOpenMap re
· 使用引理 `UpperHalfPlane.isOpenMap_norm`：isOpenMap_norm : IsOpenMap (fun τ : ℍ => 
‖(τ : Complex)‖)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Complex.one_lt_normSq_iff`：one_lt_normSq_iff {x : Complex} : 1 < normSq 
x ↔ 1 < ‖x‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Ioi
 b ↔ b < x
· 使用定理 `interior_Ici`：interior_Ici [NoMinOrder α] {a : α} : interior (Ici a) = I
oi a
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `Set.mem_of_mem_of_subset`：mem_of_mem_of_subset {x : α} {s t : Set α} (hx
 : x in s) (h : s subseteq t) : x in t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `interior_mono`：interior_mono (h : s subseteq t) : interior s subseteq in
terior t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `abs_lt`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [A
ddLeftMono α] {a b : α} [AddRightMono α],   |a| < b ↔ -b < a ∧ a < b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Set.mem_Ioo`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
oo a b ↔ a < x ∧ x < b
（共 36 条，此处仅展示前 30 条）
-/
lemma fdo_eq_interior_fd : 𝒟ᵒ = interior 𝒟 := by
  refine subset_antisymm (isOpen_fdo.subset_interior_iff.mpr fdo_subset_fd) ?_
  have ho1 := isOpenMap_re.image_interior_subset 𝒟
  have ho2 := isOpenMap_norm.image_interior_subset 𝒟
  intro x hx
  rw [Set.image_subset_iff] at *
  constructor
  · rw [one_lt_normSq_iff, ← Set.mem_Ioi, ← interior_Ici]
    apply Set.mem_of_mem_of_subset (Set.mem_preimage.mp (ho2 hx)) (interior_mono ?_)
    rw [Set.image_subset_iff]
    intro ξ hξ
    simpa [Set.mem_preimage, Set.mem_Ici, one_le_normSq_iff] using hξ.1
  · rw [abs_lt, ← Set.mem_Ioo, ← interior_Icc]
    apply Set.mem_of_mem_of_subset ((Set.mem_preimage.mp (ho1 hx))) (interior_mono ?_)
    rw [Set.image_subset_iff]
    intro ξ hξ
    simpa [Set.mem_preimage, Set.mem_Icc, abs_le] using hξ.2

end Topology

section Truncated

/-- The standard fundamental domain truncated at height `y`. -/
/-
**ModularGroup.truncatedFundamentalDomain** 是 Mathlib 中的一个定义，位于命名空间 `ModularGrou
p`。
形式化陈述：truncatedFundamentalDomain (y : Real) : Set ℍ
参数：y : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The standard fundamental domain truncated at height `y`.
-/
def truncatedFundamentalDomain (y : ℝ) : Set ℍ := { τ | τ ∈ 𝒟 ∧ τ.im ≤ y }

/-- Explicit description of the truncated fundamental domain as a subset of `ℂ`, given by
obviously closed conditions. -/
/-
**ModularGroup.coe_truncatedFundamentalDomain** 是 Mathlib 中的一个引理，位于命名空间 `Modular
Group`。
形式化陈述：coe_truncatedFundamentalDomain (y : Real) : UpperHalfPlane.coe '' truncate
dFundamentalDomain y = {z | 0 <= z.im ∧ z.im <= y ∧ |z.re| <= 1 / 2 ∧ 1 <= ‖z‖}
参数：y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Complex.normSq_eq_norm_sq`：normSq_eq_norm_sq (z : Complex) : normSq z = 
‖z‖ ^ 2
· 使用定理 `abs_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (z : E), |‖z‖| 
= ‖z‖
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `sq_lt_one_iff₀`：sq_lt_one_iff₀ (ha : 0 <= a) : a ^ 2 < 1 ↔ a < 1
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ZeroHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Zero M]
 [inst_1 : Zero N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_ze
ro' : toFun…
· 使用定理 `MonoidWithZeroHom.mk.congr_simp`：∀ {α : Type u_7} {β : Type u_8} [inst :
 MulZeroOneClass α] [inst_1 : MulZeroOneClass β]   (toZeroHom toZeroHom_1 : Zero
Hom α β) (e_toZeroHom…
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_lt_true`：isNNRat_lt_true [Semiring α] [Line
arOrder α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Nat} -> {da db : Nat}
 -> IsNNRat a na da -> IsN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
Explicit description of the truncated fundamental domain as a subset of `ℂ`, giv
en by
obviously closed conditions.
-/
lemma coe_truncatedFundamentalDomain (y : ℝ) :
    UpperHalfPlane.coe '' truncatedFundamentalDomain y =
    {z | 0 ≤ z.im ∧ z.im ≤ y ∧ |z.re| ≤ 1 / 2 ∧ 1 ≤ ‖z‖} := by
  ext z
  constructor
  · rintro ⟨⟨z, hz⟩, h, rfl⟩
    exact ⟨hz.le, h.2, h.1.2, by simpa [Complex.normSq_eq_norm_sq] using h.1.1⟩
  · rintro ⟨hz, h1, h2, h3⟩
    have hz' : 0 < z.im := by
      apply hz.lt_of_ne
      contrapose! h3
      simpa [← sq_lt_one_iff₀ (norm_nonneg _), ← Complex.normSq_eq_norm_sq, Complex.normSq,
        ← h3, ← sq] using h2.trans_lt (by norm_num)
    exact ⟨⟨z, hz'⟩, ⟨⟨by simpa [Complex.normSq_eq_norm_sq], h2⟩, h1⟩, rfl⟩

/-- For any `y : ℝ`, the standard fundamental domain truncated at height `y` is compact. -/
/-
**ModularGroup.isCompact_truncatedFundamentalDomain** 是 Mathlib 中的一个引理，位于命名空间 `M
odularGroup`。
形式化陈述：isCompact_truncatedFundamentalDomain (y : Real) : IsCompact (truncatedFund
amentalDomain y)
参数：y : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.IsEmbedding.isCompact_iff`：Topology.IsEmbedding.isCompact_iff {
f : X -> Y} (hf : IsEmbedding f) : IsCompact s ↔ IsCompact (f '' s)
· 使用定理 `UpperHalfPlane.isEmbedding_coe`：isEmbedding_coe : IsEmbedding ((↑) : ℍ -
> Complex)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `ModularGroup.coe_truncatedFundamentalDomain`：coe_truncatedFundamentalDom
ain (y : Real) : UpperHalfPlane.coe '' truncatedFundamentalDomain y = {z | 0 <= 
z.im ∧ z.im <= y ∧ |z.re| <= 1 / …
· 使用定理 `Metric.isCompact_iff_isClosed_bounded`：isCompact_iff_isClosed_bounded {α
 : Type*} {s : Set α} [MetricSpace α] [ProperSpace α] : IsCompact s ↔ IsClosed s
 ∧ IsBounded s
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `IsClosed.inter`：IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : I
sClosed (s₁ inter s₂)
· 使用定理 `isClosed_le`：isClosed_le [TopologicalSpace β] {f g : β -> α} (hf : Conti
nuous f) (hg : Continuous g) : IsClosed { b | f b <= g b }
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `Complex.continuous_im`：Continuous Complex.im
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_abs`：∀ {G : Type u_1} [inst : TopologicalSpace G] [inst_1 : A
ddCommGroup G] [inst_2 : LinearOrder G] [IsOrderedAddMonoid G]   [OrderTopology 
G], …
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Complex.continuous_re`：Continuous Complex.re
· 使用定理 `continuous_norm`：∀ {E : Type u_4} [inst : SeminormedAddGroup E], Continu
ous fun a => ‖a‖
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.isBounded_iff_subset_closedBall`：isBounded_iff_subset_closedBall 
(c : α) : IsBounded s ↔ exists r, s subseteq closedBall c r
· 使用定理 `le_of_sq_le_sq`：le_of_sq_le_sq (h : a ^ 2 <= b ^ 2) (hb : 0 <= b) : a <=
 b
· 使用定理 `Real.sq_sqrt`：sq_sqrt (h : 0 <= x) : √x ^ 2 = x
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `add_pos_of_pos_of_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst
_1 : Preorder α] [AddLeftMono α] {a b : α}, 0 < a → 0 ≤ b → 0 < a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
（共 53 条，此处仅展示前 30 条）

--- 原说明 ---
For any `y : ℝ`, the standard fundamental domain truncated at height `y` is comp
act.
-/
lemma isCompact_truncatedFundamentalDomain (y : ℝ) :
    IsCompact (truncatedFundamentalDomain y) := by
  rw [isEmbedding_coe.isCompact_iff, coe_truncatedFundamentalDomain,
    Metric.isCompact_iff_isClosed_bounded]
  constructor
  · -- show closed
    apply (isClosed_le continuous_const Complex.continuous_im).inter
    apply (isClosed_le Complex.continuous_im continuous_const).inter
    apply (isClosed_le (continuous_abs.comp Complex.continuous_re) continuous_const).inter
    exact isClosed_le continuous_const continuous_norm
  · -- show bounded
    refine (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨√((1 / 2) ^ 2 + y ^ 2), fun z hz ↦ ?_⟩
    simp only [mem_closedBall_zero_iff]
    refine le_of_sq_le_sq ?_ (by positivity)
    rw [Real.sq_sqrt (by positivity), Complex.norm_eq_sqrt_sq_add_sq, Real.sq_sqrt (by positivity)]
    apply add_le_add
    · rw [sq_le_sq, abs_of_pos <| one_half_pos (α := ℝ)]
      exact hz.2.2.1
    · rw [sq_le_sq₀ hz.1 (hz.1.trans hz.2.1)]
      exact hz.2.1


end Truncated

end FundamentalDomain

/-
**ModularGroup.exists_one_half_le_im_smul** 是 Mathlib 中的一个引理，位于命名空间 `ModularGrou
p`。
形式化陈述：exists_one_half_le_im_smul (τ : ℍ) : exists γ : SL(2, Int), 1 / 2 <= im (γ
 • τ)
参数：τ : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ModularGroup.exists_smul_mem_fd`：exists_smul_mem_fd (z : ℍ) : exists g :
 SL(2, Int), g • z in 𝒟
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
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
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
（共 86 条，此处仅展示前 30 条）
-/
lemma exists_one_half_le_im_smul (τ : ℍ) : ∃ γ : SL(2, ℤ), 1 / 2 ≤ im (γ • τ) := by
  obtain ⟨γ, hγ⟩ := exists_smul_mem_fd τ
  use γ
  nlinarith [three_le_four_mul_im_sq_of_mem_fd hγ, im_pos (γ • τ)]

/-- For every `τ : ℍ` there is some `γ ∈ SL(2, ℤ)` that sends it to an element whose
imaginary part is at least `1/2` and such that `denom γ τ` has norm at most 1. -/
/-
**ModularGroup.exists_one_half_le_im_smul_and_norm_denom_le** 是 Mathlib 中的一个引理，位
于命名空间 `ModularGroup`。
形式化陈述：exists_one_half_le_im_smul_and_norm_denom_le (τ : ℍ) : exists γ : SL(2, In
t), 1 / 2 <= im (γ • τ) ∧ ‖denom γ τ‖ <= 1
参数：τ : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用引理 `UpperHalfPlane.denom_one`：denom_one : denom 1 z = 1
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `abs_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (z : E), |‖z‖| 
= ‖z‖
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `mul_le_iff_le_one_right`：mul_le_iff_le_one_right [PosMulMono α] [PosMulR
eflectLE α] (a0 : 0 < a) : a * b <= a ↔ b <= 1
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `UpperHalfPlane.coe_im_pos`：∀ (self : UpperHalfPlane), 0 < (↑self).im
· 使用引理 `Complex.normSq_eq_norm_sq`：normSq_eq_norm_sq (z : Complex) : normSq z = 
‖z‖ ^ 2
· 使用引理 `le_div_iff₀`：le_div_iff₀ (hc : 0 < c) : a <= b / c ↔ a * c <= b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `UpperHalfPlane.normSq_denom_pos`：normSq_denom_pos (g : GL (Fin 2) Real) 
{z : Complex} (hz : z.im != 0) : 0 < Complex.normSq (denom g z)
· 使用定理 `UpperHalfPlane.im_ne_zero`：im_ne_zero (z : ℍ) : z.im != 0
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
For every `τ : ℍ` there is some `γ ∈ SL(2, ℤ)` that sends it to an element whose
imaginary part is at least `1/2` and such that `denom γ τ` has norm at most 1.
-/
lemma exists_one_half_le_im_smul_and_norm_denom_le (τ : ℍ) :
    ∃ γ : SL(2, ℤ), 1 / 2 ≤ im (γ • τ) ∧ ‖denom γ τ‖ ≤ 1 := by
  rcases le_total (1 / 2) τ.im with h | h
  · exact ⟨1, (one_smul SL(2, ℤ) τ).symm ▸ h, by
      simp only [map_one, denom_one, norm_one, le_refl]⟩
  · refine (exists_one_half_le_im_smul τ).imp (fun γ hγ ↦ ⟨hγ, ?_⟩)
    have h1 : τ.im ≤ (γ • τ).im := h.trans hγ
    rw [im_smul_eq_div_normSq, le_div_iff₀ (normSq_denom_pos γ τ.im_ne_zero),
      normSq_eq_norm_sq] at h1
    simpa only [sq_le_one_iff_abs_le_one, abs_norm] using
      (mul_le_iff_le_one_right τ.2).mp h1

end ModularGroup

