/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import Mathlib.NumberTheory.ModularForms.Cusps
public import Mathlib.NumberTheory.ModularForms.SlashActions

/-!
# Boundedness and vanishing at cusps

We define the notions of "bounded at c" and "vanishing at c" for functions on `ℍ`, where `c` is
an element of `OnePoint ℝ`.
-/

@[expose] public section

open Matrix SpecialLinearGroup UpperHalfPlane Filter Polynomial OnePoint

open scoped MatrixGroups LinearAlgebra.Projectivization ModularForm

namespace UpperHalfPlane

variable {g : GL (Fin 2) ℝ} {f : ℍ → ℂ} (k : ℤ)

/-
**UpperHalfPlane.IsZeroAtImInfty.slash** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane
.IsZeroAtImInfty`。
形式化陈述：∀ {g : GL (Fin 2) ℝ} {f : UpperHalfPlane → ℂ} (k : ℤ),   ↑g 1 0 = 0 → Uppe
rHalfPlane.IsZeroAtImInfty f → UpperHalfPlane.IsZeroAtImInfty (SlashAction.map k
 g f)
参数：Fin 2；k : ℤ；SlashAction.map k g f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UpperHalfPlane.IsZeroAtImInfty.eq_1`：∀ {α : Type u_1} [inst : Zero α] [i
nst_1 : TopologicalSpace α] (f : UpperHalfPlane → α),   UpperHalfPlane.IsZeroAtI
mInfty f = UpperHalfPlane…
· 使用定理 `Filter.ZeroAtFilter.eq_1`：∀ {α : Type u_2} {β : Type u_3} [inst : Zero β
] [inst_1 : TopologicalSpace β] (l : Filter α) (f : α → β),   l.ZeroAtFilter f =
 Filter.Tendst…
· 使用定理 `tendsto_zero_iff_norm_tendsto_zero`：∀ {α : Type u_1} {E : Type u_4} [ins
t : SeminormedAddGroup E] {f : α → E} {a : Filter α},   Filter.Tendsto f a (nhds
 0) ↔ Filter.Tendsto (fu…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.GeneralLinearGroup.val_det_apply`：∀ {n : Type u} [inst : Decidabl
eEq n] [inst_1 : Fintype n] {R : Type v} [inst_2 : CommRing R] (A : GL n R),   ↑
(Matrix.GeneralLinearGroup.de…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Complex.norm_mul`：∀ (z w : ℂ), ‖z * w‖ = ‖z‖ * ‖w‖
· 使用定理 `UpperHalfPlane.norm_σ`：∀ (g : GL (Fin 2) ℝ) (z : ℂ), ‖(UpperHalfPlane.σ 
g) z‖ = ‖z‖
· 使用定理 `norm_zpow`：norm_zpow : forall (a : α) (n : Int), ‖a ^ n‖ = ‖a‖ ^ n
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
· 使用定理 `abs_abs`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [AddL
eftMono α] [AddRightMono α] (a : α), |(|a|)| = |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用定理 `Filter.Tendsto.mul_const`：Filter.Tendsto.mul_const {α : Type*} {f : α ->
 M} {x : Filter α} {a : M} (b : M) (hf : Tendsto f x (𝓝 a)) : Tendsto (f · * b) 
x (𝓝 (a * b))
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
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用引理 `UpperHalfPlane.tendsto_smul_atImInfty`：tendsto_smul_atImInfty {g : GL (F
in 2) Real} (hg : g 1 0 = 0) : Tendsto (fun τ => g • τ) atImInfty atImInfty
-/
lemma IsZeroAtImInfty.slash (hg : g 1 0 = 0) (hf : IsZeroAtImInfty f) :
    IsZeroAtImInfty (f ∣[k] g) := by
  rw [IsZeroAtImInfty, ZeroAtFilter, tendsto_zero_iff_norm_tendsto_zero] at hf ⊢
  simpa [ModularForm.slash_def, denom, hg, mul_assoc]
    using (hf.comp <| tendsto_smul_atImInfty hg).mul_const _
/-
**UpperHalfPlane.IsBoundedAtImInfty.slash** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPl
ane.IsBoundedAtImInfty`。
形式化陈述：∀ {g : GL (Fin 2) ℝ} {f : UpperHalfPlane → ℂ} (k : ℤ),   ↑g 1 0 = 0 → Uppe
rHalfPlane.IsBoundedAtImInfty f → UpperHalfPlane.IsBoundedAtImInfty (SlashAction
.map k g f)
参数：Fin 2；k : ℤ；SlashAction.map k g f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UpperHalfPlane.IsBoundedAtImInfty.eq_1`：∀ {α : Type u_1} [inst : Norm α]
 (f : UpperHalfPlane → α),   UpperHalfPlane.IsBoundedAtImInfty f = UpperHalfPlan
e.atImInfty.BoundedAtFilter …
· 使用定理 `Filter.BoundedAtFilter.eq_1`：∀ {α : Type u_2} {β : Type u_3} [inst : Nor
m β] (l : Filter α) (f : α → β), l.BoundedAtFilter f = f =O[l] 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Asymptotics.isBigO_norm_left`：isBigO_norm_left : (fun x => ‖f' x‖) =O[l]
 g ↔ f' =O[l] g
· 使用定理 `Asymptotics.IsBigO.const_mul_left`：∀ {α : Type u_1} {F : Type u_4} {R : 
Type u_13} [inst : Norm F] [inst_1 : SeminormedRing R] {g : α → F} {l : Filter α
}   {f : α → R}, f =O[l…
· 使用定理 `Asymptotics.IsBigO.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {E : Ty
pe u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}
   {l : Filter α}, f …
· 使用引理 `UpperHalfPlane.tendsto_smul_atImInfty`：tendsto_smul_atImInfty {g : GL (F
in 2) Real} (hg : g 1 0 = 0) : Tendsto (fun τ => g • τ) atImInfty atImInfty
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.GeneralLinearGroup.val_det_apply`：∀ {n : Type u} [inst : Decidabl
eEq n] [inst_1 : Fintype n] {R : Type v} [inst_2 : CommRing R] (A : GL n R),   ↑
(Matrix.GeneralLinearGroup.de…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Complex.norm_mul`：∀ (z w : ℂ), ‖z * w‖ = ‖z‖ * ‖w‖
· 使用定理 `UpperHalfPlane.norm_σ`：∀ (g : GL (Fin 2) ℝ) (z : ℂ), ‖(UpperHalfPlane.σ 
g) z‖ = ‖z‖
· 使用定理 `norm_zpow`：norm_zpow : forall (a : α) (n : Int), ‖a ^ n‖ = ‖a‖ ^ n
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
· 使用定理 `abs_abs`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [AddL
eftMono α] [AddRightMono α] (a : α), |(|a|)| = |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
lemma IsBoundedAtImInfty.slash (hg : g 1 0 = 0) (hf : IsBoundedAtImInfty f) :
    IsBoundedAtImInfty (f ∣[k] g) := by
  rw [IsBoundedAtImInfty, BoundedAtFilter, ← Asymptotics.isBigO_norm_left] at hf ⊢
  suffices (fun x ↦ (‖g.det.val ^ (k - 1)‖ * ‖g 1 1 ^ (-k)‖) * ‖f (g • x)‖) =O[atImInfty] 1 by
    simpa [ModularForm.slash_def, denom, hg, mul_assoc, mul_comm ‖f _‖]
  apply (hf.comp_tendsto (tendsto_smul_atImInfty hg)).const_mul_left

end UpperHalfPlane

namespace OnePoint

variable (c : OnePoint ℝ) (f : ℍ → ℂ) (k : ℤ)

/-- We say `f` is bounded at `c` if, for all `g` with `g • ∞ = c`, the function `f ∣[k] g` is
bounded at `∞`. -/
/-
**OnePoint.IsBoundedAt** 是 Mathlib 中的一个定义，位于命名空间 `OnePoint`。
形式化陈述：IsBoundedAt : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say `f` is bounded at `c` if, for all `g` with `g • ∞ = c`, the function `f ∣
[k] g` is
bounded at `∞`.
-/
def IsBoundedAt : Prop := ∀ g : GL (Fin 2) ℝ, g • ∞ = c → IsBoundedAtImInfty (f ∣[k] g)

/-- We say `f` is zero at `c` if, for all `g` with `g • ∞ = c`, the function `f ∣[k] g` is
zero at `∞`. -/
/-
**OnePoint.IsZeroAt** 是 Mathlib 中的一个定义，位于命名空间 `OnePoint`。
形式化陈述：IsZeroAt : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say `f` is zero at `c` if, for all `g` with `g • ∞ = c`, the function `f ∣[k]
 g` is
zero at `∞`.
-/
def IsZeroAt : Prop := ∀ g : GL (Fin 2) ℝ, g • ∞ = c → IsZeroAtImInfty (f ∣[k] g)

variable {c f k} {g : GL (Fin 2) ℝ}
/-
**OnePoint.IsBoundedAt.smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint.IsBoundedAt`
。
形式化陈述：∀ {c : OnePoint ℝ} {f : UpperHalfPlane → ℂ} {k : ℤ} {g : GL (Fin 2) ℝ},   
(g • c).IsBoundedAt f k ↔ c.IsBoundedAt (SlashAction.map k g f) k
参数：Fin 2；g • c；SlashAction.map k g f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OnePoint.IsBoundedAt.eq_1`：∀ (c : OnePoint ℝ) (f : UpperHalfPlane → ℂ) (
k : ℤ),   c.IsBoundedAt f k =     ∀ (g : GL (Fin 2) ℝ), g • OnePoint.infty = c →
 UpperHalfPlane…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.forall_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e :
 α ≃ β), (∀ (a : α), p a) ↔ ∀ (b : β), p (e.symm b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.mulLeft_symm`：mulLeft_symm (a : G) : (Equiv.mulLeft a).symm = Equi
v.mulLeft a⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma IsBoundedAt.smul_iff : IsBoundedAt (g • c) f k ↔ IsBoundedAt c (f ∣[k] g) k := by
  rw [IsBoundedAt, IsBoundedAt, (Equiv.mulLeft g⁻¹).forall_congr_left]
  simp [mul_smul, ← SlashAction.slash_mul]
/-
**OnePoint.IsZeroAt.smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint.IsZeroAt`。
形式化陈述：∀ {c : OnePoint ℝ} {f : UpperHalfPlane → ℂ} {k : ℤ} {g : GL (Fin 2) ℝ},   
(g • c).IsZeroAt f k ↔ c.IsZeroAt (SlashAction.map k g f) k
参数：Fin 2；g • c；SlashAction.map k g f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OnePoint.IsZeroAt.eq_1`：∀ (c : OnePoint ℝ) (f : UpperHalfPlane → ℂ) (k :
 ℤ),   c.IsZeroAt f k = ∀ (g : GL (Fin 2) ℝ), g • OnePoint.infty = c → UpperHalf
Plane.IsZero…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.forall_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e :
 α ≃ β), (∀ (a : α), p a) ↔ ∀ (b : β), p (e.symm b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.mulLeft_symm`：mulLeft_symm (a : G) : (Equiv.mulLeft a).symm = Equi
v.mulLeft a⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma IsZeroAt.smul_iff : IsZeroAt (g • c) f k ↔ IsZeroAt c (f ∣[k] g) k := by
  rw [IsZeroAt, IsZeroAt, (Equiv.mulLeft g⁻¹).forall_congr_left]
  simp [mul_smul, ← SlashAction.slash_mul]
/-
**OnePoint.IsBoundedAt.add** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint.IsBoundedAt`。
形式化陈述：∀ {c : OnePoint ℝ} {f : UpperHalfPlane → ℂ} {k : ℤ} {f' : UpperHalfPlane →
 ℂ},   c.IsBoundedAt f k → c.IsBoundedAt f' k → c.IsBoundedAt (f + f') k
参数：f + f'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SlashAction.add_slash`：∀ {β : Type u_1} {G : Type u_2} {α : Type u_3} {i
nst : Monoid G} {inst_1 : AddMonoid α} [self : SlashAction β G α]   (k : β) (g :
 G) (a b : …
· 使用定理 `Filter.BoundedAtFilter.add`：∀ {α : Type u_2} {β : Type u_3} [inst : Semi
normedAddCommGroup β] {l : Filter α} {f g : α → β},   l.BoundedAtFilter f → l.Bo
undedAtFilter g …
-/
lemma IsBoundedAt.add {f' : ℍ → ℂ} (hf : IsBoundedAt c f k) (hf' : IsBoundedAt c f' k) :
    IsBoundedAt c (f + f') k :=
  fun g hg ↦ by simpa using! (hf g hg).add (hf' g hg)
/-
**OnePoint.IsZeroAt.add** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint.IsZeroAt`。
形式化陈述：∀ {c : OnePoint ℝ} {f : UpperHalfPlane → ℂ} {k : ℤ} {f' : UpperHalfPlane →
 ℂ},   c.IsZeroAt f k → c.IsZeroAt f' k → c.IsZeroAt (f + f') k
参数：f + f'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SlashAction.add_slash`：∀ {β : Type u_1} {G : Type u_2} {α : Type u_3} {i
nst : Monoid G} {inst_1 : AddMonoid α} [self : SlashAction β G α]   (k : β) (g :
 G) (a b : …
· 使用定理 `Filter.ZeroAtFilter.add`：∀ {α : Type u_2} {β : Type u_3} [inst : Topolog
icalSpace β] [inst_1 : AddZeroClass β] [ContinuousAdd β] {l : Filter α}   {f g :
 α → β}, l.Ze…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
-/
lemma IsZeroAt.add {f' : ℍ → ℂ} (hf : IsZeroAt c f k) (hf' : IsZeroAt c f' k) :
    IsZeroAt c (f + f') k :=
  fun g hg ↦ by simpa using! (hf g hg).add (hf' g hg)
/-
**OnePoint.isBoundedAt_infty_iff** 是 Mathlib 中的一个引理，位于命名空间 `OnePoint`。
形式化陈述：isBoundedAt_infty_iff : IsBoundedAt ∞ f k ↔ IsBoundedAtImInfty f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SlashAction.slash_one`：∀ {β : Type u_1} {G : Type u_2} {α : Type u_3} {i
nst : Monoid G} {inst_1 : AddMonoid α} [self : SlashAction β G α]   (k : β) (a :
 α), SlashA…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `UpperHalfPlane.IsBoundedAtImInfty.slash`：∀ {g : GL (Fin 2) ℝ} {f : Upper
HalfPlane → ℂ} (k : ℤ),   ↑g 1 0 = 0 → UpperHalfPlane.IsBoundedAtImInfty f → Upp
erHalfPlane.IsBoundedAtImInft…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `OnePoint.smul_infty_eq_self_iff`：smul_infty_eq_self_iff {g : GL (Fin 2) 
K} : g • (∞ : OnePoint K) = ∞ ↔ g 1 0 = 0
-/
lemma isBoundedAt_infty_iff : IsBoundedAt ∞ f k ↔ IsBoundedAtImInfty f :=
  ⟨fun h ↦ by simpa using h 1 (by simp), fun h _ hg ↦ h.slash _ (smul_infty_eq_self_iff.mp hg)⟩
/-
**OnePoint.isZeroAt_infty_iff** 是 Mathlib 中的一个引理，位于命名空间 `OnePoint`。
形式化陈述：isZeroAt_infty_iff : IsZeroAt ∞ f k ↔ IsZeroAtImInfty f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SlashAction.slash_one`：∀ {β : Type u_1} {G : Type u_2} {α : Type u_3} {i
nst : Monoid G} {inst_1 : AddMonoid α} [self : SlashAction β G α]   (k : β) (a :
 α), SlashA…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `UpperHalfPlane.IsZeroAtImInfty.slash`：∀ {g : GL (Fin 2) ℝ} {f : UpperHal
fPlane → ℂ} (k : ℤ),   ↑g 1 0 = 0 → UpperHalfPlane.IsZeroAtImInfty f → UpperHalf
Plane.IsZeroAtImInfty (Sla…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `OnePoint.smul_infty_eq_self_iff`：smul_infty_eq_self_iff {g : GL (Fin 2) 
K} : g • (∞ : OnePoint K) = ∞ ↔ g 1 0 = 0
-/
lemma isZeroAt_infty_iff : IsZeroAt ∞ f k ↔ IsZeroAtImInfty f :=
  ⟨fun h ↦ by simpa using h 1 (by simp), fun h _ hg ↦ h.slash _ (smul_infty_eq_self_iff.mp hg)⟩

/-- To check that `f` is bounded at `c`, it suffices for `f ∣[k] g` to be bounded at `∞` for any
single `g` with `g • ∞ = c`. -/
/-
**OnePoint.isBoundedAt_iff** 是 Mathlib 中的一个引理，位于命名空间 `OnePoint`。
形式化陈述：isBoundedAt_iff (hg : g • ∞ = c) : IsBoundedAt c f k ↔ IsBoundedAtImInfty 
(f ∣[k] g)
参数：hg : g • ∞ = c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
To check that `f` is bounded at `c`, it suffices for `f ∣[k] g` to be bounded at
 `∞` for any
single `g` with `g • ∞ = c`.
-/
lemma isBoundedAt_iff (hg : g • ∞ = c) : IsBoundedAt c f k ↔ IsBoundedAtImInfty (f ∣[k] g) :=
  ⟨fun hc ↦ hc g hg , by simp [← hg, IsBoundedAt.smul_iff, isBoundedAt_infty_iff]⟩

/-- To check that `f` is zero at `c`, it suffices for `f ∣[k] g` to be zero at `∞` for any
single `g` with `g • ∞ = c`. -/
/-
**OnePoint.isZeroAt_iff** 是 Mathlib 中的一个引理，位于命名空间 `OnePoint`。
形式化陈述：isZeroAt_iff (hg : g • ∞ = c) : IsZeroAt c f k ↔ IsZeroAtImInfty (f ∣[k] g
)
参数：hg : g • ∞ = c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
To check that `f` is zero at `c`, it suffices for `f ∣[k] g` to be zero at `∞` f
or any
single `g` with `g • ∞ = c`.
-/
lemma isZeroAt_iff (hg : g • ∞ = c) : IsZeroAt c f k ↔ IsZeroAtImInfty (f ∣[k] g) :=
  ⟨fun hc ↦ hc g hg , by simp [← hg, IsZeroAt.smul_iff, isZeroAt_infty_iff]⟩

section SL2Z

variable {c : OnePoint ℝ} {f : ℍ → ℂ} {k : ℤ}

/-
**OnePoint.isBoundedAt_iff_exists_SL2Z** 是 Mathlib 中的一个引理，位于命名空间 `OnePoint`。
形式化陈述：isBoundedAt_iff_exists_SL2Z (hc : IsCusp c 𝒮ℒ) : IsBoundedAt c f k ↔ exist
s γ : SL(2, Int), mapGL Real γ • ∞ = c ∧ IsBoundedAtImInfty (f ∣[k] γ)
参数：hc : IsCusp c 𝒮ℒ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `isCusp_SL2Z_iff'`：isCusp_SL2Z_iff' {c : OnePoint Real} : IsCusp c 𝒮ℒ ↔ e
xists g : SL(2, Int), c = mapGL Real g • ∞
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isBoundedAt_iff_exists_SL2Z (hc : IsCusp c 𝒮ℒ) :
    IsBoundedAt c f k ↔ ∃ γ : SL(2, ℤ), mapGL ℝ γ • ∞ = c ∧ IsBoundedAtImInfty (f ∣[k] γ) := by
  constructor
  · obtain ⟨γ, rfl⟩ := isCusp_SL2Z_iff'.mp hc
    simpa [IsBoundedAt.smul_iff, isBoundedAt_infty_iff] using! fun hfc ↦ ⟨γ, rfl, hfc⟩
  · rintro ⟨γ, rfl, b⟩
    simpa [IsBoundedAt.smul_iff, isBoundedAt_infty_iff] using! b
/-
**OnePoint.isZeroAt_iff_exists_SL2Z** 是 Mathlib 中的一个引理，位于命名空间 `OnePoint`。
形式化陈述：isZeroAt_iff_exists_SL2Z (hc : IsCusp c 𝒮ℒ) : IsZeroAt c f k ↔ exists γ : 
SL(2, Int), mapGL Real γ • ∞ = c ∧ IsZeroAtImInfty (f ∣[k] γ)
参数：hc : IsCusp c 𝒮ℒ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `isCusp_SL2Z_iff'`：isCusp_SL2Z_iff' {c : OnePoint Real} : IsCusp c 𝒮ℒ ↔ e
xists g : SL(2, Int), c = mapGL Real g • ∞
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isZeroAt_iff_exists_SL2Z (hc : IsCusp c 𝒮ℒ) :
    IsZeroAt c f k ↔ ∃ γ : SL(2, ℤ), mapGL ℝ γ • ∞ = c ∧ IsZeroAtImInfty (f ∣[k] γ) := by
  constructor
  · obtain ⟨γ, rfl⟩ := isCusp_SL2Z_iff'.mp hc
    simpa [IsZeroAt.smul_iff, isZeroAt_infty_iff] using! fun hfc ↦ ⟨γ, rfl, hfc⟩
  · rintro ⟨γ, rfl, b⟩
    simpa [IsZeroAt.smul_iff, isZeroAt_infty_iff] using! b
/-
**OnePoint.isBoundedAt_iff_forall_SL2Z** 是 Mathlib 中的一个引理，位于命名空间 `OnePoint`。
形式化陈述：isBoundedAt_iff_forall_SL2Z (hc : IsCusp c 𝒮ℒ) : IsBoundedAt c f k ↔ foral
l γ : SL(2, Int), mapGL Real γ • ∞ = c -> IsBoundedAtImInfty (f ∣[k] γ)
参数：hc : IsCusp c 𝒮ℒ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `isCusp_SL2Z_iff'`：isCusp_SL2Z_iff' {c : OnePoint Real} : IsCusp c 𝒮ℒ ↔ e
xists g : SL(2, Int), c = mapGL Real g • ∞
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isBoundedAt_iff_forall_SL2Z (hc : IsCusp c 𝒮ℒ) :
    IsBoundedAt c f k ↔ ∀ γ : SL(2, ℤ), mapGL ℝ γ • ∞ = c → IsBoundedAtImInfty (f ∣[k] γ) := by
  refine ⟨fun hc _ hγ ↦ by simpa using! hc _ hγ, fun h ↦ ?_⟩
  obtain ⟨γ, rfl⟩ := isCusp_SL2Z_iff'.mp hc
  simpa [IsBoundedAt.smul_iff, isBoundedAt_infty_iff] using! h γ rfl
/-
**OnePoint.isZeroAt_iff_forall_SL2Z** 是 Mathlib 中的一个引理，位于命名空间 `OnePoint`。
形式化陈述：isZeroAt_iff_forall_SL2Z (hc : IsCusp c 𝒮ℒ) : IsZeroAt c f k ↔ forall γ : 
SL(2, Int), mapGL Real γ • ∞ = c -> IsZeroAtImInfty (f ∣[k] γ)
参数：hc : IsCusp c 𝒮ℒ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `isCusp_SL2Z_iff'`：isCusp_SL2Z_iff' {c : OnePoint Real} : IsCusp c 𝒮ℒ ↔ e
xists g : SL(2, Int), c = mapGL Real g • ∞
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isZeroAt_iff_forall_SL2Z (hc : IsCusp c 𝒮ℒ) :
    IsZeroAt c f k ↔ ∀ γ : SL(2, ℤ), mapGL ℝ γ • ∞ = c → IsZeroAtImInfty (f ∣[k] γ) := by
  refine ⟨fun hc _ hγ ↦ by simpa using! hc _ hγ, fun h ↦ ?_⟩
  obtain ⟨γ, rfl⟩ := isCusp_SL2Z_iff'.mp hc
  simpa [IsZeroAt.smul_iff, isZeroAt_infty_iff] using! h γ rfl

end SL2Z

end OnePoint

