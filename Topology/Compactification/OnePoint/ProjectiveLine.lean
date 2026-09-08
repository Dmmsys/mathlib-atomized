/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen, Oliver Nash
-/
module

public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.LinearAlgebra.Matrix.Action
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# One-point compactification and projectivization

We construct a set-theoretic equivalence between
`OnePoint K` and the projectivization `ℙ K (Fin 2 → K)` for an arbitrary division ring `K`.

TODO: Add the extension of this equivalence to a homeomorphism in the case `K = ℝ`,
where `OnePoint ℝ` gets the topology of one-point compactification.


## Main definitions and results

* `OnePoint.equivProjectivization` : the equivalence `OnePoint K ≃ ℙ K (Fin 2 → K)`.

## Tags

one-point extension, projectivization
-/

@[expose] public section

open scoped LinearAlgebra.Projectivization

open Projectivization Matrix Polynomial OnePoint

section MatrixProdAction

variable {R n : Type*} [Semiring R] [Fintype n] [DecidableEq n]

/-
**Matrix.mulVec_fin_two** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] (m : Matrix (Fin 2) (Fin 2) R) (v : F
in 2 → R),   m.mulVec v = ![m 0 0 * v 0 + m 0 1 * v 1, m 1 0 * v 0 + m 1 1 * v 1
]
参数：m : Matrix (Fin 2) (Fin 2) R；v : Fin 2 → R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.mulVec_eq_sum`：mulVec_eq_sum [Fintype n] (v : n -> α) (M : Matrix
 m n α) : M *ᵥ v = ∑ i, MulOpposite.op (v i) • Mᵀ i
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Fin.sum_univ_two`：∀ {M : Type u_2} [inst : AddCommMonoid M] (f : Fin 2 →
 M), ∑ i, f i = f 0 + f 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
@[simp] lemma Matrix.mulVec_fin_two (m : Matrix (Fin 2) (Fin 2) R) (v : Fin 2 → R) :
    m *ᵥ v = ![m 0 0 * v 0 + m 0 1 * v 1, m 1 0 * v 0 + m 1 1 * v 1] := by
  ext i
  fin_cases i <;>
  simp [mulVec_eq_sum]
/-
**Matrix.GeneralLinearGroup.fin_two_smul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Gener
alLinearGroup`。
形式化陈述：∀ {R : Type u_3} [inst : CommRing R] (g : GL (Fin 2) R) (v : Fin 2 → R),  
 g • v = ![↑g 0 0 * v 0 + ↑g 0 1 * v 1, ↑g 1 0 * v 0 + ↑g 1 1 * v 1]
参数：g : GL (Fin 2) R；v : Fin 2 → R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.mulVec_fin_two`：∀ {R : Type u_1} [inst : Semiring R] (m : Matrix 
(Fin 2) (Fin 2) R) (v : Fin 2 → R),   m.mulVec v = ![m 0 0 * v 0 + m 0 1 * v 1, 
m 1 0 * v 0…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma Matrix.GeneralLinearGroup.fin_two_smul {R : Type*} [CommRing R]
    (g : GL (Fin 2) R) (v : Fin 2 → R) :
    g • v = ![g 0 0 * v 0 + g 0 1 * v 1, g 1 0 * v 0 + g 1 1 * v 1] := by
  simp [Units.smul_def]

@[deprecated "use Fin 2 → R instead" (since := "2026-04-19")]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module (Matrix (Fin 2) (Fin 2) R) (R × R) :=
  (LinearEquiv.finTwoArrow R R).symm.toAddEquiv.module _

@[deprecated "use Fin 2 → R instead" (since := "2026-04-19")]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {S} [DistribSMul S R] [SMulCommClass R S R] :
    SMulCommClass (Matrix (Fin 2) (Fin 2) R) S (R × R) :=
  (LinearEquiv.finTwoArrow R R).symm.smulCommClass _ _

set_option backward.isDefEq.respectTransparency.types false in
@[deprecated "use Fin 2 → R instead" (since := "2026-04-19")]
/-
**Matrix.fin_two_smul_prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Matrix.fin_two_smul_prod (g : Matrix (Fin 2) (Fin 2) R) (v : R × R) : g • 
v = (g 0 0 * v.1 + g 0 1 * v.2, g 1 0 * v.1 + g 1 1 * v.2)
参数：g : Matrix (Fin 2) (Fin 2) R；v : R × R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `LinearEquiv.right_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semirin
g R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPa
ir σ σ'] [i…
· 使用定理 `LinearEquiv.finTwoArrow_apply`：∀ (R : Type u) (M : Type v) [inst : Semir
ing R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   ⇑(LinearEquiv.
finTwoArrow R M) = …
· 使用定理 `LinearEquiv.finTwoArrow_symm_apply`：∀ (R : Type u) (M : Type v) [inst : 
Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   ⇑(LinearE
quiv.finTwoArrow R M).sy…
· 使用定理 `LinearEquiv.left_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semiring
 R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPai
r σ σ'] [i…
· 使用定理 `Equiv.mk.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} (toFun toFun_1 : α 
→ β) (e_toFun : toFun = toFun_1) (invFun invFun_1 : β → α)   (e_invFun : invFun 
= invFun_…
· 使用定理 `Matrix.mulVec_eq_sum`：mulVec_eq_sum [Fintype n] (v : n -> α) (M : Matrix
 m n α) : M *ᵥ v = ∑ i, MulOpposite.op (v i) • Mᵀ i
· 使用定理 `Fin.sum_univ_two`：∀ {M : Type u_2} [inst : AddCommMonoid M] (f : Fin 2 →
 M), ∑ i, f i = f 0 + f 1
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Matrix.fin_two_smul_prod (g : Matrix (Fin 2) (Fin 2) R) (v : R × R) :
    g • v = (g 0 0 * v.1 + g 0 1 * v.2, g 1 0 * v.1 + g 1 1 * v.2) := by
  simp [Equiv.smul_def, smul_eq_mulVec, Matrix.mulVec_eq_sum]

@[deprecated Matrix.GeneralLinearGroup.fin_two_smul (since := "2026-04-19")]
/-
**Matrix.GeneralLinearGroup.fin_two_smul_prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Matrix.GeneralLinearGroup.fin_two_smul_prod {R : Type*} [CommRing R] (g : 
GL (Fin 2) R) (v : R × R) : g • v = (g 0 0 * v.1 + g 0 1 * v.2, g 1 0 * v.1 + g 
1 1 * v.2)
参数：g : GL (Fin 2) R；v : R × R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matrix.fin_two_smul_prod`：Matrix.fin_two_smul_prod (g : Matrix (Fin 2) (
Fin 2) R) (v : R × R) : g • v = (g 0 0 * v.1 + g 0 1 * v.2, g 1 0 * v.1 + g 1 1 
* v.2)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Matrix.GeneralLinearGroup.fin_two_smul_prod {R : Type*} [CommRing R]
    (g : GL (Fin 2) R) (v : R × R) :
    g • v = (g 0 0 * v.1 + g 0 1 * v.2, g 1 0 * v.1 + g 1 1 * v.2) := by
  simp [Units.smul_def, Matrix.fin_two_smul_prod]

end MatrixProdAction

namespace OnePoint

section DivisionRing

variable (K : Type*) [DivisionRing K] [DecidableEq K]

/-- The one-point compactification of a division ring `K` is equivalent to
the projectivization `ℙ K (Fin 2 → K)`. -/
/-
**OnePoint.equivProjectivization** 是 Mathlib 中的一个定义，位于命名空间 `OnePoint`。
形式化陈述：equivProjectivization : OnePoint K ≃ ℙ K (Fin 2 -> K) where toFun p
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The one-point compactification of a division ring `K` is equivalent to
the projectivization `ℙ K (Fin 2 → K)`.
-/
def equivProjectivization : OnePoint K ≃ ℙ K (Fin 2 → K) where
  toFun p := p.elim (mk K ![1, 0] (by simp)) (fun t ↦ mk K ![t, 1] (by simp))
  invFun p := by
    refine Projectivization.lift
      (fun u : {v : Fin 2 → K // v ≠ 0} ↦ if u.1 1 = 0 then ∞ else ((u.1 1)⁻¹ * u.1 0)) ?_ p
    rintro ⟨-, hv⟩ ⟨w, hw⟩ t rfl
    have ht : t ≠ 0 := by rintro rfl; simp at hv
    by_cases h₀ : w 1 = 0 <;> simp [h₀, ht, mul_assoc]
  left_inv p := by cases p <;> simp
  right_inv p := by
    induction p using ind with | h w hw =>
    by_cases h₀ : w 1 = 0 <;> simp only [mk_eq_mk_iff', h₀, Projectivization.lift_mk, if_true,
        if_false, OnePoint.elim_infty, OnePoint.elim_some]
    · have : w 0 ≠ 0 := fun h ↦ hw <| funext <| by simp_all
      use (w 0)⁻¹
      ext i
      fin_cases i <;> simp_all
    · exact ⟨(w 1)⁻¹, funext <| by simp [inv_mul_cancel₀ h₀]⟩

@[simp]
/-
**OnePoint.equivProjectivization_apply_infinity** 是 Mathlib 中的一个引理，位于命名空间 `OnePo
int`。
形式化陈述：equivProjectivization_apply_infinity : equivProjectivization K ∞ = mk K ![
1, 0] (by simp)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma equivProjectivization_apply_infinity :
    equivProjectivization K ∞ = mk K ![1, 0] (by simp) :=
  rfl

@[simp]
/-
**OnePoint.equivProjectivization_apply_coe** 是 Mathlib 中的一个引理，位于命名空间 `OnePoint`。
形式化陈述：equivProjectivization_apply_coe (t : K) : equivProjectivization K t = mk K
 ![t, 1] (by simp)
参数：t : K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma equivProjectivization_apply_coe (t : K) :
    equivProjectivization K t = mk K ![t, 1] (by simp) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**OnePoint.equivProjectivization_symm_apply_mk** 是 Mathlib 中的一个引理，位于命名空间 `OnePoi
nt`。
形式化陈述：equivProjectivization_symm_apply_mk (v : Fin 2 -> K) (h : v != 0) : (equiv
Projectivization K).symm (mk K v h) = if v 1 = 0 then ∞ else (v 1)⁻¹ * v 0
参数：v : Fin 2 -> K；h : v != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Projectivization.lift.congr_simp`：∀ {K : Type u_1} {V : Type u_2} [inst 
: DivisionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]   {α : 
Type u_3} (f f_1 : { v…
· 使用定理 `Equiv.mk.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} (toFun toFun_1 : α 
→ β) (e_toFun : toFun = toFun_1) (invFun invFun_1 : β → α)   (e_invFun : invFun 
= invFun_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma equivProjectivization_symm_apply_mk (v : Fin 2 → K) (h : v ≠ 0) :
    (equivProjectivization K).symm (mk K v h) = if v 1 = 0 then ∞ else (v 1)⁻¹ * v 0 := by
  simp [equivProjectivization]

end DivisionRing

section Field

variable {K : Type*} [Field K] [DecidableEq K]

/-- For a field `K`, the group `GL(2, K)` acts on `OnePoint K`, via the canonical identification
with the `ℙ¹(K)` (which is given explicitly by Möbius transformations). -/
/-
**OnePoint.instGLAction** 是 Mathlib 中的一个实例，位于命名空间 `OnePoint`。
形式化陈述：instGLAction : MulAction (GL (Fin 2) K) (OnePoint K)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a field `K`, the group `GL(2, K)` acts on `OnePoint K`, via the canonical id
entification
with the `ℙ¹(K)` (which is given explicitly by Möbius transformations).
-/
instance instGLAction : MulAction (GL (Fin 2) K) (OnePoint K) :=
  (equivProjectivization K).mulAction (GL (Fin 2) K)
/-
**OnePoint.equivProjectivization_smul** 是 Mathlib 中的一个引理，位于命名空间 `OnePoint`。
形式化陈述：equivProjectivization_smul {g : GL (Fin 2) K} (x : OnePoint K) : equivProj
ectivization K (g • x) = g • equivProjectivization K x
参数：Fin 2；x : OnePoint K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.instSMulCommClassForall`：∀ {n : Type u_1} {R : Type u_2} {S : Typ
e u_3} [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : Semiring R]   [inst
_3 : DistribSMul S R…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.smul_def`：∀ {M : Type u_1} {α : Type u_2} {β : Type u_3} (e : α ≃ 
β) [inst : SMul M β] (n : M) (x : α), n • x = e.symm (n • e x)
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
lemma equivProjectivization_smul {g : GL (Fin 2) K} (x : OnePoint K) :
    equivProjectivization K (g • x) = g • equivProjectivization K x := by
  rw [Equiv.smul_def, Equiv.apply_symm_apply]

set_option backward.isDefEq.respectTransparency.types false in
/-
**OnePoint.smul_infty_def** 是 Mathlib 中的一个引理，位于命名空间 `OnePoint`。
形式化陈述：smul_infty_def {g : GL (Fin 2) K} : g • ∞ = (equivProjectivization K).symm
 (.mk K ![g 0 0, g 1 0] (fun h => by simpa [det_fin_two, show g 0 0 = 0 from con
gr_fun h 0, show g 1 0 = 0 from congr_fun h 1] using g.det_ne_zero))
参数：Fin 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `smul_ne_zero_iff_ne`：smul_ne_zero_iff_ne (a : α) {x : β} : a • x != 0 ↔ 
x != 0
· 使用定理 `Matrix.mulVec_eq_sum`：mulVec_eq_sum [Fintype n] (v : n -> α) (M : Matrix
 m n α) : M *ᵥ v = ∑ i, MulOpposite.op (v i) • Mᵀ i
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `IsCentralScalar.op_smul_eq_smul`：∀ {M : Type u_9} {α : Type u_10} {inst 
: SMul M α} {inst_1 : SMul Mᵐᵒᵖ α} [self : IsCentralScalar M α] (m : M) (a : α),
   MulOpposite.op m •…
· 使用定理 `Fin.sum_univ_two`：∀ {M : Type u_2} [inst : AddCommMonoid M] (f : Fin 2 →
 M), ∑ i, f i = f 0 + f 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Projectivization.mk.congr_simp`：∀ (K : Type u_1) {V : Type u_2} [inst : 
DivisionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]   (v v_1 
: V) (e_v : v = v_1)…
· 使用引理 `OnePoint.equivProjectivization_symm_apply_mk`：equivProjectivization_symm
_apply_mk (v : Fin 2 -> K) (h : v != 0) : (equivProjectivization K).symm (mk K v
 h) = if v 1 = 0 then ∞ else (v 1)…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma smul_infty_def {g : GL (Fin 2) K} :
    g • ∞ = (equivProjectivization K).symm (.mk K ![g 0 0, g 1 0] (fun h ↦ by
      simpa [det_fin_two, show g 0 0 = 0 from congr_fun h 0, show g 1 0 = 0 from congr_fun h 1]
        using g.det_ne_zero)) := by
  simp [Equiv.smul_def, mulVec_eq_sum, Units.smul_def]
/-
**OnePoint.smul_infty_eq_ite** 是 Mathlib 中的一个引理，位于命名空间 `OnePoint`。
形式化陈述：smul_infty_eq_ite (g : GL (Fin 2) K) : g • (∞ : OnePoint K) = if g 1 0 = 0
 then ∞ else g 0 0 / g 1 0
参数：g : GL (Fin 2) K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `OnePoint.smul_infty_def`：smul_infty_def {g : GL (Fin 2) K} : g • ∞ = (eq
uivProjectivization K).symm (.mk K ![g 0 0, g 1 0] (fun h => by simpa [det_fin_t
wo, show g 0 …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Projectivization.mk.congr_simp`：∀ (K : Type u_1) {V : Type u_2} [inst : 
DivisionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]   (v v_1 
: V) (e_v : v = v_1)…
· 使用引理 `OnePoint.equivProjectivization_symm_apply_mk`：equivProjectivization_symm
_apply_mk (v : Fin 2 -> K) (h : v != 0) : (equivProjectivization K).symm (mk K v
 h) = if v 1 = 0 then ∞ else (v 1)…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
-/
lemma smul_infty_eq_ite (g : GL (Fin 2) K) :
    g • (∞ : OnePoint K) = if g 1 0 = 0 then ∞ else g 0 0 / g 1 0 := by
  by_cases h : g 1 0 = 0 <;>
  simp [h, div_eq_inv_mul, smul_infty_def]
/-
**OnePoint.smul_infty_eq_self_iff** 是 Mathlib 中的一个引理，位于命名空间 `OnePoint`。
形式化陈述：smul_infty_eq_self_iff {g : GL (Fin 2) K} : g • (∞ : OnePoint K) = ∞ ↔ g 1
 0 = 0
参数：Fin 2。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `OnePoint.smul_infty_eq_ite`：smul_infty_eq_ite (g : GL (Fin 2) K) : g • (
∞ : OnePoint K) = if g 1 0 = 0 then ∞ else g 0 0 / g 1 0
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma smul_infty_eq_self_iff {g : GL (Fin 2) K} :
    g • (∞ : OnePoint K) = ∞ ↔ g 1 0 = 0 := by
  simp [smul_infty_eq_ite]
/-
**OnePoint.smul_some_eq_ite** 是 Mathlib 中的一个引理，位于命名空间 `OnePoint`。
形式化陈述：smul_some_eq_ite {g : GL (Fin 2) K} {k : K} : g • (k : OnePoint K) = if g 
1 0 * k + g 1 1 = 0 then ∞ else (g 0 0 * k + g 0 1) / (g 1 0 * k + g 1 1)
参数：Fin 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `smul_ne_zero_iff_ne`：smul_ne_zero_iff_ne (a : α) {x : β} : a • x != 0 ↔ 
x != 0
· 使用定理 `Matrix.mulVec_eq_sum`：mulVec_eq_sum [Fintype n] (v : n -> α) (M : Matrix
 m n α) : M *ᵥ v = ∑ i, MulOpposite.op (v i) • Mᵀ i
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `IsCentralScalar.op_smul_eq_smul`：∀ {M : Type u_9} {α : Type u_10} {inst 
: SMul M α} {inst_1 : SMul Mᵐᵒᵖ α} [self : IsCentralScalar M α] (m : M) (a : α),
   MulOpposite.op m •…
· 使用定理 `Fin.sum_univ_two`：∀ {M : Type u_2} [inst : AddCommMonoid M] (f : Fin 2 →
 M), ∑ i, f i = f 0 + f 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Projectivization.mk.congr_simp`：∀ (K : Type u_1) {V : Type u_2} [inst : 
DivisionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]   (v v_1 
: V) (e_v : v = v_1)…
· 使用引理 `OnePoint.equivProjectivization_symm_apply_mk`：equivProjectivization_symm
_apply_mk (v : Fin 2 -> K) (h : v != 0) : (equivProjectivization K).symm (mk K v
 h) = if v 1 = 0 then ∞ else (v 1)…
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma smul_some_eq_ite {g : GL (Fin 2) K} {k : K} :
    g • (k : OnePoint K) =
      if g 1 0 * k + g 1 1 = 0 then ∞ else (g 0 0 * k + g 0 1) / (g 1 0 * k + g 1 1) := by
  simp [Equiv.smul_def, mulVec_eq_sum, div_eq_inv_mul, mul_comm, Units.smul_def]
/-
**OnePoint.map_smul** 是 Mathlib 中的一个引理，位于命名空间 `OnePoint`。
形式化陈述：map_smul {L : Type*} [Field L] [DecidableEq L] (f : K ->+* L) (g : GL (Fin
 2) K) (c : OnePoint K) : OnePoint.map f (g • c) = (g.map f) • (c.map f)
参数：f : K ->+* L；g : GL (Fin 2) K；c : OnePoint K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `OnePoint.smul_infty_eq_ite`：smul_infty_eq_ite (g : GL (Fin 2) K) : g • (
∞ : OnePoint K) = if g 1 0 = 0 then ∞ else g 0 0 / g 1 0
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.GeneralLinearGroup.map_apply`：∀ {n : Type u} [inst : DecidableEq 
n] [inst_1 : Fintype n] {R : Type v} [inst_2 : CommRing R] {S : Type u_1}   [ins
t_3 : CommRing S] (f : R …
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `OnePoint.smul_some_eq_ite`：smul_some_eq_ite {g : GL (Fin 2) K} {k : K} :
 g • (k : OnePoint K) = if g 1 0 * k + g 1 1 = 0 then ∞ else (g 0 0 * k + g 0 1)
 / (g 1 0 * k +…
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
-/
lemma map_smul {L : Type*} [Field L] [DecidableEq L]
    (f : K →+* L) (g : GL (Fin 2) K) (c : OnePoint K) :
    OnePoint.map f (g • c) = (g.map f) • (c.map f) := by
  cases c with
  | infty => simp [smul_infty_eq_ite, apply_ite]
  | coe c => simp [smul_some_eq_ite, ← map_mul, ← map_add, apply_ite]

end Field

end OnePoint

namespace Matrix.GeneralLinearGroup

variable {K : Type*} [Field K] [DecidableEq K]

/-- The roots of `g.fixpointPolynomial` are the fixed points of `g ∈ GL(2, K)` acting on the finite
part of `OnePoint K`.

See also `gl_smul_eq_self_iff_quadratic` for a similar lemma
about the fixed points of the action of `GL(2, ℝ)` on the upper half-plane. -/
/-
**Matrix.GeneralLinearGroup.fixpointPolynomial_aeval_eq_zero_iff** 是 Mathlib 中的一
个引理，位于命名空间 `Matrix.GeneralLinearGroup`。
形式化陈述：fixpointPolynomial_aeval_eq_zero_iff {c : K} {g : GL (Fin 2) K} : g.fixpoi
ntPolynomial.aeval c = 0 ↔ g • (c : OnePoint K) = c
参数：Fin 2。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `Polynomial.aeval_X_pow`：aeval_X_pow {n : Nat} : aeval x ((X : R[X]) ^ n)
 = x ^ n
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用引理 `OnePoint.smul_some_eq_ite`：smul_some_eq_ite {g : GL (Fin 2) K} {k : K} :
 g • (k : OnePoint K) = if g 1 0 * k + g 1 1 = 0 then ∞ else (g 0 0 * k + g 0 1)
 / (g 1 0 * k +…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用引理 `Matrix.GeneralLinearGroup.det_ne_zero`：det_ne_zero [Nontrivial R] (g : G
L n R) : g.val.det != 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Matrix.det_fin_two`：det_fin_two (A : Matrix (Fin 2) (Fin 2) R) : det A =
 A 0 0 * A 1 1 - A 0 1 * A 1 0
· 使用定理 `OnePoint.infty_ne_coe`：infty_ne_coe (x : X) : ∞ != (x : OnePoint X)
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `OnePoint.coe_eq_coe`：coe_eq_coe {x y : X} : (x : OnePoint X) = y ↔ x = y
· 使用引理 `div_eq_iff`：div_eq_iff (hb : b != 0) : a / b = c ↔ a = c * b

--- 原说明 ---
The roots of `g.fixpointPolynomial` are the fixed points of `g ∈ GL(2, K)` actin
g on the finite
part of `OnePoint K`.

See also `gl_smul_eq_self_iff_quadratic` for a similar lemma
about the fixed points of the action of `GL(2, ℝ)` on the upper half-plane.
-/
lemma fixpointPolynomial_aeval_eq_zero_iff {c : K} {g : GL (Fin 2) K} :
    g.fixpointPolynomial.aeval c = 0 ↔ g • (c : OnePoint K) = c := by
  simp only [fixpointPolynomial, map_sub, map_mul, map_add, aeval_X_pow, aeval_C, aeval_X,
    Algebra.algebraMap_self_apply, OnePoint.smul_some_eq_ite]
  split_ifs with h
  · refine ⟨fun hg ↦ (g.det_ne_zero ?_).elim, fun hg ↦ (infty_ne_coe _ hg).elim⟩
    rw [det_fin_two]
    grind
  · rw [coe_eq_coe, div_eq_iff h]
    grind

/-- If `g` is parabolic, this is the unique fixed point of `g` in `OnePoint K`. -/
/-
**Matrix.GeneralLinearGroup.parabolicFixedPoint** 是 Mathlib 中的一个定义，位于命名空间 `Matri
x.GeneralLinearGroup`。
形式化陈述：parabolicFixedPoint (g : GL (Fin 2) K) : OnePoint K
参数：g : GL (Fin 2) K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `g` is parabolic, this is the unique fixed point of `g` in `OnePoint K`.
-/
def parabolicFixedPoint (g : GL (Fin 2) K) : OnePoint K :=
  if g 1 0 = 0 then ∞ else ↑((g 0 0 - g 1 1) / (2 * g 1 0))
/-
**Matrix.GeneralLinearGroup.IsParabolic.smul_eq_self_iff** 是 Mathlib 中的一个定理，位于命名
空间 `Matrix.GeneralLinearGroup.IsParabolic`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] [inst_1 : DecidableEq K] {g : GL (Fin 2)
 K},   g.IsParabolic → ∀ [NeZero 2] {c : OnePoint K}, g • c = c ↔ c = g.paraboli
cFixedPoint
参数：Fin 2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `OnePoint.smul_infty_eq_ite`：smul_infty_eq_ite (g : GL (Fin 2) K) : g • (
∞ : OnePoint K) = if g 1 0 = 0 then ∞ else g 0 0 / g 1 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.det_fin_two`：det_fin_two (A : Matrix (Fin 2) (Fin 2) R) : det A =
 A 0 0 * A 1 1 - A 0 1 * A 1 0
· 使用定理 `Matrix.trace_fin_two`：trace_fin_two (A : Matrix (Fin 2) (Fin 2) R) : tra
ce A = A 0 0 + A 1 1
· 使用引理 `Matrix.discr_fin_two`：discr_fin_two (A : Matrix (Fin 2) (Fin 2) R) : A.d
iscr = A.trace ^ 2 - 4 * A.det
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `Matrix.GeneralLinearGroup.fixpointPolynomial_eq_zero_iff`：fixpointPolyno
mial_eq_zero_iff {g : GL (Fin 2) R} : g.fixpointPolynomial = 0 ↔ g.val in Set.ra
nge (Matrix.scalar _)
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `discrim.eq_1`：∀ {R : Type u_1} [inst : Ring R] (a b c : R), discrim a b 
c = b ^ 2 - 4 * a * c
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
（共 46 条，此处仅展示前 30 条）
-/
lemma IsParabolic.smul_eq_self_iff {g : GL (Fin 2) K} (hg : g.IsParabolic) [NeZero (2 : K)]
    {c : OnePoint K} : g • c = c ↔ c = parabolicFixedPoint g := by
  rcases hg with ⟨hg, hdisc⟩
  rw [discr_fin_two, trace_fin_two, det_fin_two] at hdisc
  cases c with
  | infty => by_cases h : g 1 0 = 0 <;> simp [parabolicFixedPoint, smul_infty_eq_ite, h]
  | coe c =>
    suffices g 1 0 * c ^ 2 + (g 1 1 - g 0 0) * c - g 0 1 = 0 ↔ c = g.parabolicFixedPoint by
      simpa [← fixpointPolynomial_aeval_eq_zero_iff, fixpointPolynomial]
    by_cases hc : g 1 0 = 0
    · have hd : g 1 1 = g 0 0 := by grind
      suffices g 0 1 ≠ 0 by simpa [parabolicFixedPoint, hc, hd]
      -- can't have `g 0 1 ≠ 0` since that would force `g` to be scalar
      refine fun hb ↦ fixpointPolynomial_eq_zero_iff.not.mpr hg ?_
      simp [fixpointPolynomial, hb, hc, hd]
    · have : discrim (g 1 0) (g 1 1 - g 0 0) (-g 0 1) = 0 := by rw [discrim]; grind
      simpa [parabolicFixedPoint, if_neg hc, sq, sub_eq_add_neg]
        using quadratic_eq_zero_iff_of_discrim_eq_zero hc this c
/-
**Matrix.GeneralLinearGroup.IsParabolic.parabolicFixedPoint_pow** 是 Mathlib 中的一个
定理，位于命名空间 `Matrix.GeneralLinearGroup.IsParabolic`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] [inst_1 : DecidableEq K] {g : GL (Fin 2)
 K},   g.IsParabolic → ∀ [CharZero K] {n : ℕ}, n ≠ 0 → (g ^ n).parabolicFixedPoi
nt = g.parabolicFixedPoint
参数：Fin 2；g ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.GeneralLinearGroup.IsParabolic.smul_eq_self_iff`：∀ {K : Type u_1}
 [inst : Field K] [inst_1 : DecidableEq K] {g : GL (Fin 2) K},   g.IsParabolic →
 ∀ [NeZero 2] {c : OnePoint K}, g • c = c ↔ …
· 使用定理 `Matrix.GeneralLinearGroup.IsParabolic.pow`：∀ {K : Type u_2} [inst : Fiel
d K] {g : GL (Fin 2) K},   g.IsParabolic → ∀ [CharZero K] {n : ℕ}, n ≠ 0 → (g ^ 
n).IsParabolic
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
lemma IsParabolic.parabolicFixedPoint_pow {g : GL (Fin 2) K} (hg : IsParabolic g) [CharZero K]
    {n : ℕ} (hn : n ≠ 0) :
    (g ^ n).parabolicFixedPoint = g.parabolicFixedPoint := by
  rw [eq_comm, ← IsParabolic.smul_eq_self_iff (hg.pow hn)]
  clear hn
  induction n with
  | zero => simp
  | succ n IH => rw [pow_succ, mul_smul, hg.smul_eq_self_iff.mpr rfl, IH]

/-- Elliptic elements have no fixed points in `OnePoint K`. -/
/-
**Matrix.GeneralLinearGroup.IsElliptic.smul_ne_self** 是 Mathlib 中的一个定理，位于命名空间 `M
atrix.GeneralLinearGroup.IsElliptic`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] [inst_1 : DecidableEq K] [inst_2 : Linea
rOrder K] [IsStrictOrderedRing K]   {g : GL (Fin 2) K}, g.IsElliptic → ∀ (c : On
ePoint K), g • c ≠ c
参数：Fin 2；c : OnePoint K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `OnePoint.smul_infty_eq_self_iff`：smul_infty_eq_self_iff {g : GL (Fin 2) 
K} : g • (∞ : OnePoint K) = ∞ ↔ g 1 0 = 0
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Matrix.discr_fin_two`：discr_fin_two (A : Matrix (Fin 2) (Fin 2) R) : A.d
iscr = A.trace ^ 2 - 4 * A.det
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.trace_fin_two`：trace_fin_two (A : Matrix (Fin 2) (Fin 2) R) : tra
ce A = A 0 0 + A 1 1
· 使用定理 `Matrix.det_fin_two`：det_fin_two (A : Matrix (Fin 2) (Fin 2) R) : det A =
 A 0 0 * A 1 1 - A 0 1 * A 1 0
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Polynomial.eval_neg`：eval_neg (p : R[X]) (x : R) : (-p).eval x = -p.eval
 x
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
Elliptic elements have no fixed points in `OnePoint K`.
-/
lemma IsElliptic.smul_ne_self [LinearOrder K] [IsStrictOrderedRing K]
    {g : GL (Fin 2) K} (hg : g.IsElliptic) (c : OnePoint K) :
    g • c ≠ c := by
  cases c with
  | infty =>
    rw [Ne, smul_infty_eq_self_iff]
    refine fun h ↦ not_le_of_gt hg ?_
    have : g.val.discr = (g 0 0 - g 1 1) ^ 2 := by
      simp only [discr_fin_two, trace_fin_two, det_fin_two]
      grind
    rw [this]
    apply sq_nonneg
  | coe c =>
    refine fun h ↦ not_le_of_gt hg ?_
    have : g.val.discr = (2 * g 1 0 * c + (g 1 1 + -g 0 0)) ^ 2 := by
      replace h : g 1 0 * (c * c) + (g 1 1 + -g 0 0) * c + -g 0 1 = 0 := by
        simpa [← fixpointPolynomial_aeval_eq_zero_iff, fixpointPolynomial, sq, sub_eq_add_neg]
          using h
      simp only [← discrim_eq_sq_of_quadratic_eq_zero h, discr_fin_two, discrim, trace_fin_two,
        det_fin_two]
      grind
    rw [this]
    apply sq_nonneg

end Matrix.GeneralLinearGroup

