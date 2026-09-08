/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.ModularForms.SlashInvariantForms
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.NumberTheory.ModularForms.Cusps

/-!
# Identities of ModularForms and SlashInvariantForms

Collection of useful identities of modular forms.
-/

public section

noncomputable section

open ModularForm UpperHalfPlane Matrix CongruenceSubgroup Matrix.SpecialLinearGroup MatrixGroups

namespace SlashInvariantForm

/-
**SlashInvariantForm.vAdd_apply_of_mem_strictPeriods** 是 Mathlib 中的一个定理，位于命名空间 `
SlashInvariantForm`。
形式化陈述：vAdd_apply_of_mem_strictPeriods {Γ : Subgroup (GL (Fin 2) Real)} {k : Int}
 {F : Type*} [FunLike F ℍ Complex] [SlashInvariantFormClass F Γ k] (f : F) (τ : 
ℍ) {h : Real} (hH : h in Γ.strictPeriods) : f (h +ᵥ τ) = f τ
参数：GL (Fin 2) Real；f : F；τ : ℍ；hH : h in Γ.strictPeriods。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `SlashInvariantForm.slash_action_eqn`：slash_action_eqn [SlashInvariantFor
mClass F Γ k] (f : F) (γ) (hγ : γ in Γ) : ↑f ∣[k] γ = ⇑f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.mem_strictPeriods_iff`：∀ {R : Type u_1} [inst : Ring R] {𝒢 : Su
bgroup (GL (Fin 2) R)} {x : R},   x ∈ 𝒢.strictPeriods ↔ Matrix.GeneralLinearGrou
p.upperRightHom x ∈ …
· 使用定理 `UpperHalfPlane.ext`：∀ {x y : UpperHalfPlane}, ↑x = ↑y → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.GeneralLinearGroup.upperRightHom_apply`：∀ {R : Type u_1} [inst : 
Ring R] (x : R),   Matrix.GeneralLinearGroup.upperRightHom x =     { val := !![1
, x; 0, 1], inv := !![1, -x; 0, 1],…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Matrix.GeneralLinearGroup.val_det_apply`：∀ {n : Type u} [inst : Decidabl
eEq n] [inst_1 : Fintype n] {R : Type v} [inst_2 : CommRing R] (A : GL n R),   ↑
(Matrix.GeneralLinearGroup.de…
· 使用定理 `Matrix.det_fin_two_of`：det_fin_two_of (a b c d : R) : Matrix.det !![a, b
; c, d] = a * d - b * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
（共 33 条，此处仅展示前 30 条）
-/
theorem vAdd_apply_of_mem_strictPeriods {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    {F : Type*} [FunLike F ℍ ℂ] [SlashInvariantFormClass F Γ k]
    (f : F) (τ : ℍ) {h : ℝ} (hH : h ∈ Γ.strictPeriods) :
    f (h +ᵥ τ) = f τ := by
  rw [← congr_fun (slash_action_eqn f _ <| Γ.mem_strictPeriods_iff.mp hH) τ]
  suffices GeneralLinearGroup.upperRightHom h • τ = h +ᵥ τ by
    simp_rw [slash_def, this]
    simp [σ, denom, GeneralLinearGroup.val_det_apply, denom]
  ext
  simp [σ, num, denom, coe_vadd, UpperHalfPlane.coe_smul, num, add_comm]
/-
**SlashInvariantForm.vAdd_width_periodic** 是 Mathlib 中的一个定理，位于命名空间 `SlashInvaria
ntForm`。
形式化陈述：vAdd_width_periodic (N : Nat) (k n : Int) (f : SlashInvariantForm (Gamma N
) k) (z : ℍ) : f ((N * n : Real) +ᵥ z) = f z
参数：N : Nat；k n : Int；f : SlashInvariantForm (Gamma N) k；z : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SlashInvariantForm.vAdd_apply_of_mem_strictPeriods`：vAdd_apply_of_mem_st
rictPeriods {Γ : Subgroup (GL (Fin 2) Real)} {k : Int} {F : Type*} [FunLike F ℍ 
Complex] [SlashInvariantFormClass F Γ k]…
· 使用定理 `SlashInvariantFormClass.slashInvariantForm`：∀ (Γ : outParam (Subgroup (G
L (Fin 2) ℝ))) (k : outParam ℤ), SlashInvariantFormClass (SlashInvariantForm Γ k
) Γ k
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CongruenceSubgroup.strictPeriods_Gamma`：∀ (N : ℕ),   (Subgroup.map (Matr
ix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma N)).strictPeriods =    
 AddSubgroup.zmultiples ↑N
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem vAdd_width_periodic (N : ℕ) (k n : ℤ) (f : SlashInvariantForm (Gamma N) k) (z : ℍ) :
    f ((N * n : ℝ) +ᵥ z) = f z := by
  apply vAdd_apply_of_mem_strictPeriods
  simp [strictPeriods_Gamma, AddSubgroup.mem_zmultiples_iff, mul_comm]
/-
**SlashInvariantForm.T_zpow_width_invariant** 是 Mathlib 中的一个定理，位于命名空间 `SlashInva
riantForm`。
形式化陈述：T_zpow_width_invariant (N : Nat) (k n : Int) (f : SlashInvariantForm (Gamm
a N) k) (z : ℍ) : f (((ModularGroup.T ^ (N * n))) • z) = f z
参数：N : Nat；k n : Int；f : SlashInvariantForm (Gamma N) k；z : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UpperHalfPlane.modular_T_zpow_smul`：modular_T_zpow_smul (z : ℍ) (n : Int
) : ModularGroup.T ^ n • z = (n : Real) +ᵥ z
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `SlashInvariantForm.vAdd_width_periodic`：vAdd_width_periodic (N : Nat) (k
 n : Int) (f : SlashInvariantForm (Gamma N) k) (z : ℍ) : f ((N * n : Real) +ᵥ z)
 = f z
-/
theorem T_zpow_width_invariant (N : ℕ) (k n : ℤ) (f : SlashInvariantForm (Gamma N) k) (z : ℍ) :
    f (((ModularGroup.T ^ (N * n))) • z) = f z := by
  rw [modular_T_zpow_smul z (N * n)]
  simpa only [Int.cast_mul, Int.cast_natCast] using vAdd_width_periodic N k n f z

set_option backward.isDefEq.respectTransparency.types false in
/-
**SlashInvariantForm.slash_S_apply** 是 Mathlib 中的一个引理，位于命名空间 `SlashInvariantForm
`。
形式化陈述：slash_S_apply (f : ℍ -> Complex) (k : Int) (z : ℍ) : (f ∣[k] ModularGroup.
S) z = f (.mk _ z.im_inv_neg_coe_pos) * z ^ (-k)
参数：f : ℍ -> Complex；k : Int；z : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperHalfPlane.im_inv_neg_coe_pos`：im_inv_neg_coe_pos (z : ℍ) : 0 < (-z 
: Complex)⁻¹.im
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ModularForm.SL_slash_apply`：SL_slash_apply (γ : SL(2, Int)) (τ : ℍ) : (f
 ∣[k] γ) τ = f (γ • τ) * denom γ τ ^ (-k)
· 使用定理 `UpperHalfPlane.modular_S_smul`：modular_S_smul (z : ℍ) : ModularGroup.S •
 z = mk (-z : Complex)⁻¹ z.im_inv_neg_coe_pos
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `inv_neg`：inv_neg : (-a)⁻¹ = -a⁻¹
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `UpperHalfPlane.mk.congr_simp`：∀ (coe coe_1 : ℂ) (e_coe : coe = coe_1) (c
oe_im_pos : 0 < coe.im),   { coe := coe, coe_im_pos := coe_im_pos } = { coe := c
oe_1, coe_im_pos :…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.SpecialLinearGroup.map_apply_coe`：∀ {n : Type u} [inst : Decidabl
eEq n] [inst_1 : Fintype n] {R : Type v} [inst_2 : CommRing R] {S : Type u_1}   
[inst_3 : CommRing S] (f : R …
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma slash_S_apply (f : ℍ → ℂ) (k : ℤ) (z : ℍ) :
    (f ∣[k] ModularGroup.S) z = f (.mk _ z.im_inv_neg_coe_pos) * z ^ (-k) := by
  rw [SL_slash_apply, modular_S_smul]
  simp [ModularGroup.S, denom]

section Generators

/-
**SlashInvariantForm.slash_action_generators** 是 Mathlib 中的一个定理，位于命名空间 `SlashInv
ariantForm`。
形式化陈述：slash_action_generators {f : ℍ -> Complex} {Γ : Subgroup (GL (Fin 2) Real)
} {s : Set (GL (Fin 2) Real)} (hΓ : Γ = Subgroup.closure s) {k : Int} : (forall 
γ in Γ, f ∣[k] γ = f) ↔ (forall γ in s, f ∣[k] γ = f)
参数：GL (Fin 2) Real；GL (Fin 2) Real；hΓ : Γ = Subgroup.closure s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.mem_closure_of_mem`：mem_closure_of_mem {s : Set G} {x : G} (hx 
: x in s) : x in closure s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.closure_induction`：closure_induction {p : (g : G) -> g in closu
re k -> Prop} (mem : forall x (hx : x in k), p x (subset_closure hx)) (one : p 1
 (one_mem _)) (m…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SlashAction.slash_one`：∀ {β : Type u_1} {G : Type u_2} {α : Type u_3} {i
nst : Monoid G} {inst_1 : AddMonoid α} [self : SlashAction β G α]   (k : β) (a :
 α), SlashA…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `SlashAction.slash_mul`：∀ {β : Type u_1} {G : Type u_2} {α : Type u_3} {i
nst : Monoid G} {inst_1 : AddMonoid α} [self : SlashAction β G α]   (k : β) (g h
 : G) (a : …
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
-/
theorem slash_action_generators {f : ℍ → ℂ} {Γ : Subgroup (GL (Fin 2) ℝ)}
    {s : Set (GL (Fin 2) ℝ)} (hΓ : Γ = Subgroup.closure s) {k : ℤ} :
    (∀ γ ∈ Γ, f ∣[k] γ = f) ↔ (∀ γ ∈ s, f ∣[k] γ = f) := by
  constructor <;> intro h γ hγ
  · exact h γ (hΓ ▸ Subgroup.mem_closure_of_mem hγ)
  · apply Subgroup.closure_induction (p := fun γ _ ↦ f ∣[k] γ = f) h (by simp)
    · simp +contextual [SlashAction.slash_mul]
    · intro x hx hf
      rw [← hf, ← SlashAction.slash_mul]
      simp [hf]
    · simpa [← hΓ]

end Generators

end SlashInvariantForm

