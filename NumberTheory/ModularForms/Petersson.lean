/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# The Petersson scalar product

For `f, f'` functions `ℍ → ℂ`, we define `petersson k f f'` to be the function
`τ ↦ conj (f τ) * f' τ * τ.im ^ k`.

We show this function is (weight 0) invariant under `Γ` if `f, f'` are (weight `k`) invariant under
`Γ`.
-/

@[expose] public section


open UpperHalfPlane Asymptotics Filter

open scoped MatrixGroups ComplexConjugate ModularForm

namespace UpperHalfPlane

/-- The integrand in the Petersson scalar product of two modular forms. -/
/-
**UpperHalfPlane.petersson** 是 Mathlib 中的一个定义，位于命名空间 `UpperHalfPlane`。
形式化陈述：petersson (k : Int) (f f' : ℍ -> Complex) (τ : ℍ)
参数：k : Int；f f' : ℍ -> Complex；τ : ℍ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The integrand in the Petersson scalar product of two modular forms.
-/
noncomputable def petersson (k : ℤ) (f f' : ℍ → ℂ) (τ : ℍ) :=
  conj (f τ) * f' τ * τ.im ^ k

@[fun_prop]
/-
**UpperHalfPlane.petersson_continuous** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`
。
形式化陈述：petersson_continuous (k : Int) {f f' : ℍ -> Complex} (hf : Continuous f) (
hf' : Continuous f') : Continuous (petersson k f f')
参数：k : Int；hf : Continuous f；hf' : Continuous f'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_mul`：continuous_mul : Continuous fun p : M × M => p.1 * p.2
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `Complex.continuous_conj`：Continuous ⇑(starRingEnd ℂ)
· 使用定理 `Continuous.zpow₀`：Continuous.zpow₀ (hf : Continuous f) (m : Int) (h0 : f
orall a, f a != 0 ∨ 0 <= m) : Continuous fun x => f x ^ m
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
· 使用定理 `UpperHalfPlane.continuous_im`：continuous_im : Continuous im
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `UpperHalfPlane.im_ne_zero`：im_ne_zero (z : ℍ) : z.im != 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma petersson_continuous (k : ℤ) {f f' : ℍ → ℂ} (hf : Continuous f) (hf' : Continuous f') :
    Continuous (petersson k f f') := by
  unfold petersson
  fun_prop (disch := simp [im_ne_zero _])
/-
**UpperHalfPlane.petersson_slash** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：petersson_slash (k : Int) (f f' : ℍ -> Complex) (g : GL (Fin 2) Real) (τ :
 ℍ) : petersson k (f ∣[k] g) (f' ∣[k] g) τ = |g.det.val| ^ (k - 2) * σ g (peters
son k f f' (g • τ))
参数：k : Int；f f' : ℍ -> Complex；g : GL (Fin 2) Real；τ : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_ne_zero`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder 
α] [AddLeftMono α] {a : α} [AddRightMono α], |a| ≠ 0 ↔ a ≠ 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `Matrix.GeneralLinearGroup.det_ne_zero`：det_ne_zero [Nontrivial R] (g : G
L n R) : g.val.det != 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `map_zpow₀`：map_zpow₀ {F G₀ G₀' : Type*} [GroupWithZero G₀] [GroupWithZer
o G₀'] [FunLike F G₀ G₀'] [MonoidWithZeroHomClass F G₀ G₀'] (f : F) (x : G₀) (n…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Complex.conj_ofReal`：conj_ofReal (r : Real) : conj (r : Complex) = r
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `_private.Mathlib.NumberTheory.ModularForms.Petersson.0.UpperHalfPlane.pe
tersson_slash._abel_1_1`：∀ (k : ℤ), k - 2 + k = k - 1 + (k - 1)
· 使用引理 `zpow_add₀`：zpow_add₀ (ha : a != 0) (m n : Int) : a ^ (m + n) = a ^ m * a
 ^ n
· 使用定理 `Complex.normSq_eq_conj_mul_self`：normSq_eq_conj_mul_self {z : Complex} :
 (normSq z : Complex) = conj z * z
· 使用定理 `mul_zpow`：∀ {α : Type u_1} [inst : DivisionCommMonoid α] (a b : α) (n : 
ℤ), (a * b) ^ n = a ^ n * b ^ n
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
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
（共 59 条，此处仅展示前 30 条）
-/
lemma petersson_slash (k : ℤ) (f f' : ℍ → ℂ) (g : GL (Fin 2) ℝ) (τ : ℍ) :
    petersson k (f ∣[k] g) (f' ∣[k] g) τ =
      |g.det.val| ^ (k - 2) * σ g (petersson k f f' (g • τ)) := by
  set D := |g.det.val|
  have hD : (D : ℂ) ≠ 0 := mod_cast abs_ne_zero.mpr g.det_ne_zero
  set j := denom g τ
  calc petersson k (f ∣[k] g) (f' ∣[k] g) τ
  _ = D ^ (k - 2 + k) * conj (σ g (f (g • τ))) * σ g (f' (g • τ))
      * (τ.im ^ k * j.normSq ^ (-k)) := by
    simp [Complex.normSq_eq_conj_mul_self, (by abel : k - 2 + k = (k - 1) + (k - 1)), petersson,
      zpow_add₀ hD, mul_zpow, ModularForm.slash_def, -Matrix.GeneralLinearGroup.val_det_apply]
    ring
  _ = D ^ (k - 2) * (conj (σ g (f (g • τ))) * σ g (f' (g • τ)) * (D * τ.im / j.normSq) ^ k) := by
    rw [div_zpow, mul_zpow, zpow_neg, div_eq_mul_inv, zpow_add₀ hD]
    ring
  _ = D ^ (k - 2) * (conj (σ g (f (g • τ))) * σ g (f' (g • τ)) * (im (g • τ)) ^ k) := by
    rw [im_smul_eq_div_normSq, Complex.ofReal_div, Complex.ofReal_mul]
  _ = D ^ (k - 2) * σ g (petersson k f f' (g • τ)) := by simp [petersson, σ_conj]
/-
**UpperHalfPlane.petersson_slash_SL** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：petersson_slash_SL (k : Int) (f f' : ℍ -> Complex) (g : SL(2, Int)) (τ : ℍ
) : petersson k (f ∣[k] g) (f' ∣[k] g) τ = petersson k f f' (g • τ)
参数：k : Int；f f' : ℍ -> Complex；g : SL(2, Int)；τ : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `UpperHalfPlane.petersson_slash`：petersson_slash (k : Int) (f f' : ℍ -> C
omplex) (g : GL (Fin 2) Real) (τ : ℍ) : petersson k (f ∣[k] g) (f' ∣[k] g) τ = |
g.det.val| ^ (k - 2)…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.SpecialLinearGroup.coeToGL_det`：coeToGL_det (g : SpecialLinearGro
up n R) : Matrix.GeneralLinearGroup.det (g : GL n R) = 1
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `one_zpow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (n : ℤ), 1 ^ n = 1
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma petersson_slash_SL (k : ℤ) (f f' : ℍ → ℂ) (g : SL(2, ℤ)) (τ : ℍ) :
    petersson k (f ∣[k] g) (f' ∣[k] g) τ = petersson k f f' (g • τ) := by
  -- need to disable a simp lemma as it works against `Matrix.SpecialLinearGroup.det_coe`
  simp [σ, ModularForm.SL_slash, petersson_slash,
    -Matrix.SpecialLinearGroup.map_apply_coe]
/-
**UpperHalfPlane.petersson_symm** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：petersson_symm (k : Int) (f f' : ℍ -> Complex) (τ : ℍ) : petersson k f' f 
τ = conj (petersson k f f' τ)
参数：k : Int；f f' : ℍ -> Complex；τ : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `map_zpow₀`：map_zpow₀ {F G₀ G₀' : Type*} [GroupWithZero G₀] [GroupWithZer
o G₀'] [FunLike F G₀ G₀'] [MonoidWithZeroHomClass F G₀ G₀'] (f : F) (x : G₀) (n…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Complex.conj_ofReal`：conj_ofReal (r : Real) : conj (r : Complex) = r
· 使用定理 `RingHomCompTriple.comp_apply`：comp_apply [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
 {x : R₁} : σ₂₃ (σ₁₂ x) = σ₁₃ x
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma petersson_symm (k : ℤ) (f f' : ℍ → ℂ) (τ : ℍ) :
    petersson k f' f τ = conj (petersson k f f' τ) := by
  simp [petersson, mul_comm]
/-
**UpperHalfPlane.petersson_norm_symm** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：petersson_norm_symm (k : Int) (f f' : ℍ -> Complex) (τ : ℍ) : ‖petersson k
 f' f τ‖ = ‖petersson k f f' τ‖
参数：k : Int；f f' : ℍ -> Complex；τ : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `UpperHalfPlane.petersson_symm`：petersson_symm (k : Int) (f f' : ℍ -> Com
plex) (τ : ℍ) : petersson k f' f τ = conj (petersson k f f' τ)
· 使用定理 `RCLike.norm_conj`：norm_conj (z : K) : ‖conj z‖ = ‖z‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma petersson_norm_symm (k : ℤ) (f f' : ℍ → ℂ) (τ : ℍ) :
    ‖petersson k f' f τ‖ = ‖petersson k f f' τ‖ := by
  simp [petersson_symm k f]

end UpperHalfPlane

section

variable {F F' : Type*} [FunLike F ℍ ℂ] [FunLike F' ℍ ℂ]

/-
**SlashInvariantFormClass.norm_petersson_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SlashInvariantFormClass.norm_petersson_smul {k g τ} {Γ : Subgroup (GL (Fin
 2) Real)} [Γ.HasDetPlusMinusOne] [SlashInvariantFormClass F Γ k] {f : F} [Slash
InvariantFormClass F' Γ k] {f' : F'} (hg : g in Γ) : ‖petersson k f f' (g • τ)‖ 
= ‖petersson k f f' τ‖
参数：GL (Fin 2) Real；hg : g in Γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SlashInvariantFormClass.slash_action_eq`：∀ {F : Type u_1} {Γ : outParam 
(Subgroup (GL (Fin 2) ℝ))} {k : outParam ℤ} {inst : FunLike F UpperHalfPlane ℂ} 
  [self : SlashInvariantFormC…
· 使用引理 `UpperHalfPlane.petersson_slash`：petersson_slash (k : Int) (f f' : ℍ -> C
omplex) (g : GL (Fin 2) Real) (τ : ℍ) : petersson k (f ∣[k] g) (f' ∣[k] g) τ = |
g.det.val| ^ (k - 2)…
· 使用定理 `Subgroup.HasDetPlusMinusOne.abs_det`：∀ {n : Type u_1} [inst : Fintype n]
 [inst_1 : DecidableEq n] {R : Type u_2} [inst_2 : CommRing R]   {Γ : Subgroup (
GL n R)} [inst_3 : Linear…
· 使用定理 `Complex.ofReal_one`：ofReal_one : ((1 : Real) : Complex) = 1
· 使用定理 `one_zpow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (n : ℤ), 1 ^ n = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `UpperHalfPlane.norm_σ`：∀ (g : GL (Fin 2) ℝ) (z : ℂ), ‖(UpperHalfPlane.σ 
g) z‖ = ‖z‖
-/
lemma SlashInvariantFormClass.norm_petersson_smul {k g τ} {Γ : Subgroup (GL (Fin 2) ℝ)}
    [Γ.HasDetPlusMinusOne] [SlashInvariantFormClass F Γ k] {f : F}
    [SlashInvariantFormClass F' Γ k] {f' : F'} (hg : g ∈ Γ) :
    ‖petersson k f f' (g • τ)‖ = ‖petersson k f f' τ‖ := by
  conv_rhs => rw [← slash_action_eq f _ hg, ← slash_action_eq f' _ hg, petersson_slash,
    Subgroup.HasDetPlusMinusOne.abs_det hg, Complex.ofReal_one, one_zpow, one_mul, norm_σ]
/-
**SlashInvariantFormClass.petersson_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SlashInvariantFormClass.petersson_smul {k g τ} {Γ : Subgroup (GL (Fin 2) R
eal)} [Γ.HasDetOne] [SlashInvariantFormClass F Γ k] {f : F} [SlashInvariantFormC
lass F' Γ k] {f' : F'} (hg : g in Γ) : petersson k f f' (g • τ) = petersson k f 
f' τ
参数：GL (Fin 2) Real；hg : g in Γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subgroup.HasDetOne.det_eq`：∀ {n : Type u_1} {inst : Fintype n} {inst_1 :
 DecidableEq n} {R : Type u_2} {inst_2 : CommRing R}   {Γ : Subgroup (GL n R)} [
self : Γ.HasDet…
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `one_zpow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (n : ℤ), 1 ^ n = 1
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `SlashInvariantFormClass.slash_action_eq`：∀ {F : Type u_1} {Γ : outParam 
(Subgroup (GL (Fin 2) ℝ))} {k : outParam ℤ} {inst : FunLike F UpperHalfPlane ℂ} 
  [self : SlashInvariantFormC…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `UpperHalfPlane.petersson_slash`：petersson_slash (k : Int) (f f' : ℍ -> C
omplex) (g : GL (Fin 2) Real) (τ : ℍ) : petersson k (f ∣[k] g) (f' ∣[k] g) τ = |
g.det.val| ^ (k - 2)…
-/
lemma SlashInvariantFormClass.petersson_smul {k g τ} {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne]
    [SlashInvariantFormClass F Γ k] {f : F} [SlashInvariantFormClass F' Γ k] {f' : F'}
    (hg : g ∈ Γ) : petersson k f f' (g • τ) = petersson k f f' τ := by
  simpa [SlashInvariantFormClass.slash_action_eq _ _ hg, Subgroup.HasDetOne.det_eq hg, σ]
    using (petersson_slash k f f' g τ).symm

namespace UpperHalfPlane.IsZeroAtImInfty

variable (k : ℤ) (Γ : Subgroup (GL (Fin 2) ℝ))
    [Fact (IsCusp OnePoint.infty Γ)] [Γ.HasDetPlusMinusOne] [DiscreteTopology Γ]
    [ModularFormClass F Γ k] [ModularFormClass F' Γ k]

include Γ -- can't be inferred from statements

/-- If `f, f'` are modular forms and `f` is zero at infinity, then `petersson k f f'` has
exponentially rapid decay at infinity. -/
/-
**UpperHalfPlane.IsZeroAtImInfty.petersson_exp_decay_left** 是 Mathlib 中的一个引理，位于命
名空间 `UpperHalfPlane.IsZeroAtImInfty`。
形式化陈述：petersson_exp_decay_left {f : F} (h_bd : IsZeroAtImInfty f) (f' : F') : ex
ists a > 0, petersson k f f' =O[atImInfty] fun τ => Real.exp (-a * im τ)
参数：h_bd : IsZeroAtImInfty f；f' : F'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModularFormClass.exp_decay_atImInfty'`：∀ {k : ℤ} {F : Type u_1} [inst : 
FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} (f : F)   [ModularForm
Class F Γ k] [Γ.HasDetPlusM…
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
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
· 使用定理 `Asymptotics.IsBigO.of_norm_left`：∀ {α : Type u_1} {F : Type u_4} {E' : T
ype u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {f' 
: α → E'} {l : Filter…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Complex.norm_conj`：norm_conj (z : Complex) : ‖conj z‖ = ‖z‖
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `norm_zpow`：norm_zpow : forall (a : α) (n : Int), ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `ModularFormClass.bdd_at_infty`：ModularFormClass.bdd_at_infty [ModularFor
mClass F Γ k] [Fact (IsCusp ∞ Γ)] : IsBoundedAtImInfty f
· 使用定理 `Asymptotics.IsBigO.mul`：∀ {α : Type u_1} {R : Type u_13} [inst : Seminor
medRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   {l : Filte
r α} {f₁ f₂ …
· 使用定理 `Asymptotics.IsBigO.norm_left`：∀ {α : Type u_1} {F : Type u_4} {E' : Type
 u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {f' : α
 → E'} {l : Filter…
· 使用定理 `Asymptotics.IsBigO.trans`：∀ {α : Type u_1} {E : Type u_3} {G : Type u_5}
 {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : SeminormedAddComm
Group F'] {l :…
· 使用定理 `Asymptotics.isBigO_refl`：isBigO_refl (f : α -> E) (l : Filter α) : f =O[
l] f
· 使用定理 `Asymptotics.IsBigO.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {E : Ty
pe u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}
   {l : Filter α}, f …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
If `f, f'` are modular forms and `f` is zero at infinity, then `petersson k f f'
` has
exponentially rapid decay at infinity.
-/
lemma petersson_exp_decay_left {f : F} (h_bd : IsZeroAtImInfty f) (f' : F') :
    ∃ a > 0, petersson k f f' =O[atImInfty] fun τ ↦ Real.exp (-a * im τ) := by
  obtain ⟨b, hb, hbf⟩ := ModularFormClass.exp_decay_atImInfty' f h_bd
  obtain ⟨a, ha, ha'⟩ := exists_between hb
  use a, ha
  apply IsBigO.of_norm_left
  simp_rw [petersson, norm_mul, Complex.norm_conj, mul_comm ‖f _‖ ‖f' _‖, norm_zpow, mul_assoc,
      Complex.norm_real, Real.norm_of_nonneg (fun {τ : ℍ} ↦ τ.im_pos).le]
  conv_rhs => enter [τ]; rw [← one_mul (Real.exp _)]
  have hf' : IsBoundedAtImInfty f' := ModularFormClass.bdd_at_infty f'
  refine hf'.norm_left.mul ((hbf.norm_left.mul <| isBigO_refl _ _).trans ?_)
  refine IsBigO.comp_tendsto (f := fun t : ℝ ↦ Real.exp (-b * t) * t ^ k)
     (g := fun t : ℝ ↦ Real.exp (-a * t)) ?_ tendsto_comap
  simpa using (isLittleO_exp_mul_rpow_of_lt k (neg_lt_neg ha')).isBigO

/-- If `f, f'` are modular forms and `f'` is zero at infinity, then `petersson k f f'` has
exponentially rapid decay at infinity. -/
/-
**UpperHalfPlane.IsZeroAtImInfty.petersson_exp_decay_right** 是 Mathlib 中的一个引理，位于
命名空间 `UpperHalfPlane.IsZeroAtImInfty`。
形式化陈述：petersson_exp_decay_right (f : F) {f' : F'} (h_bd : IsZeroAtImInfty f') : 
exists a > 0, petersson k f f' =O[atImInfty] fun τ => Real.exp (-a * im τ)
参数：f : F；h_bd : IsZeroAtImInfty f'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `UpperHalfPlane.IsZeroAtImInfty.petersson_exp_decay_left`：petersson_exp_d
ecay_left {f : F} (h_bd : IsZeroAtImInfty f) (f' : F') : exists a > 0, petersson
 k f f' =O[atImInfty] fun τ => Real.exp (-a *…
· 使用定理 `Asymptotics.IsBigO.of_norm_left`：∀ {α : Type u_1} {F : Type u_4} {E' : T
ype u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {f' 
: α → E'} {l : Filter…
· 使用定理 `Asymptotics.IsBigO.congr_left`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {g : α → F} {l : Filter α}   {f₁ f₂ : α 
→ E}, f₁ =O[l] g → …
· 使用定理 `Asymptotics.IsBigO.norm_left`：∀ {α : Type u_1} {F : Type u_4} {E' : Type
 u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {f' : α
 → E'} {l : Filter…
· 使用引理 `UpperHalfPlane.petersson_norm_symm`：petersson_norm_symm (k : Int) (f f' 
: ℍ -> Complex) (τ : ℍ) : ‖petersson k f' f τ‖ = ‖petersson k f f' τ‖

--- 原说明 ---
If `f, f'` are modular forms and `f'` is zero at infinity, then `petersson k f f
'` has
exponentially rapid decay at infinity.
-/
lemma petersson_exp_decay_right (f : F) {f' : F'} (h_bd : IsZeroAtImInfty f') :
    ∃ a > 0, petersson k f f' =O[atImInfty] fun τ ↦ Real.exp (-a * im τ) := by
  obtain ⟨a, ha, ha'⟩ := h_bd.petersson_exp_decay_left k Γ f
  exact ⟨a, ha, .of_norm_left <| ha'.norm_left.congr_left <| petersson_norm_symm k f f'⟩

omit Γ in
-- this lemma can't go in `UpperHalfPlane.FunctionsBoundedAtInfty` because it needs `Real.exp`
/-
**UpperHalfPlane.IsZeroAtImInfty.of_exp_decay** 是 Mathlib 中的一个引理，位于命名空间 `UpperHa
lfPlane.IsZeroAtImInfty`。
形式化陈述：of_exp_decay {E : Type*} [NormedAddCommGroup E] {f : ℍ -> E} (hf : exists 
c > 0, f =O[atImInfty] fun τ => Real.exp (-c * τ.im)) : IsZeroAtImInfty f
参数：hf : exists c > 0, f =O[atImInfty] fun τ => Real.exp (-c * τ.im)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.trans_tendsto`：∀ {α : Type u_1} {E'' : Type u_9} {F''
 : Type u_10} [inst : NormedAddCommGroup E''] [inst_1 : NormedAddCommGroup F''] 
  {f'' : α → E''} {g''…
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Real.tendsto_exp_atBot`：tendsto_exp_atBot : Tendsto exp atBot (𝓝 0)
· 使用定理 `Filter.Tendsto.const_mul_atTop_of_neg`：∀ {α : Type u_1} {β : Type u_2} [
inst : Field α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α] {l : Filter β} 
  {f : β → α} {r : α}, r < …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_lt_zero`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeft
StrictMono α] {a : α}, -a < 0 ↔ 0 < a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `Filter.tendsto_comap`：tendsto_comap {f : α -> β} {x : Filter β} : Tendst
o f (comap f x) x
-/
lemma of_exp_decay {E : Type*} [NormedAddCommGroup E] {f : ℍ → E}
    (hf : ∃ c > 0, f =O[atImInfty] fun τ ↦ Real.exp (-c * τ.im)) :
    IsZeroAtImInfty f := by
  obtain ⟨a, ha, ha'⟩ := hf
  refine ha'.trans_tendsto <| (Real.tendsto_exp_atBot.comp ?_).comp tendsto_comap
  exact tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr ha)
/-
**UpperHalfPlane.IsZeroAtImInfty.petersson_isZeroAtImInfty_left** 是 Mathlib 中的一个
引理，位于命名空间 `UpperHalfPlane.IsZeroAtImInfty`。
形式化陈述：petersson_isZeroAtImInfty_left {f : F} (h_bd : IsZeroAtImInfty f) (f' : F'
) : IsZeroAtImInfty (petersson k f f')
参数：h_bd : IsZeroAtImInfty f；f' : F'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `UpperHalfPlane.IsZeroAtImInfty.of_exp_decay`：of_exp_decay {E : Type*} [N
ormedAddCommGroup E] {f : ℍ -> E} (hf : exists c > 0, f =O[atImInfty] fun τ => R
eal.exp (-c * τ.im)) : IsZeroAtIm…
· 使用引理 `UpperHalfPlane.IsZeroAtImInfty.petersson_exp_decay_left`：petersson_exp_d
ecay_left {f : F} (h_bd : IsZeroAtImInfty f) (f' : F') : exists a > 0, petersson
 k f f' =O[atImInfty] fun τ => Real.exp (-a *…
-/
lemma petersson_isZeroAtImInfty_left {f : F} (h_bd : IsZeroAtImInfty f) (f' : F') :
    IsZeroAtImInfty (petersson k f f') :=
  of_exp_decay (h_bd.petersson_exp_decay_left k Γ f')
/-
**UpperHalfPlane.IsZeroAtImInfty.petersson_isZeroAtImInfty_right** 是 Mathlib 中的一
个引理，位于命名空间 `UpperHalfPlane.IsZeroAtImInfty`。
形式化陈述：petersson_isZeroAtImInfty_right (f : F) {f' : F'} (h_bd : IsZeroAtImInfty 
f') : IsZeroAtImInfty (petersson k f f')
参数：f : F；h_bd : IsZeroAtImInfty f'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `UpperHalfPlane.IsZeroAtImInfty.of_exp_decay`：of_exp_decay {E : Type*} [N
ormedAddCommGroup E] {f : ℍ -> E} (hf : exists c > 0, f =O[atImInfty] fun τ => R
eal.exp (-c * τ.im)) : IsZeroAtIm…
· 使用引理 `UpperHalfPlane.IsZeroAtImInfty.petersson_exp_decay_right`：petersson_exp_
decay_right (f : F) {f' : F'} (h_bd : IsZeroAtImInfty f') : exists a > 0, peters
son k f f' =O[atImInfty] fun τ => Real.exp (-a…
-/
lemma petersson_isZeroAtImInfty_right (f : F) {f' : F'} (h_bd : IsZeroAtImInfty f') :
    IsZeroAtImInfty (petersson k f f') :=
  of_exp_decay (h_bd.petersson_exp_decay_right k Γ f)

end UpperHalfPlane.IsZeroAtImInfty

end

