/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.SemiringInverse
public import Mathlib.LinearAlgebra.InvariantBasisNumber

/-!
# Invertible matrices over a ring with invariant basis number are square.
-/

public section

section

open Function Matrix LinearMap

variable {R : Type*} [Semiring R]

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [OrzechProperty R] : IsStablyFiniteRing R :=
  isStablyFiniteRing_iff_injective_of_surjective.mpr fun _ ↦
    OrzechProperty.injective_of_surjective_endomorphism
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [IsStablyFiniteRing R] [Nontrivial R] : RankCondition R where
  le_of_fin_surjective {n m} f hf := by
    by_contra! lt
    let p : (Fin m → R) →ₗ[R] Fin n → R := funLeft R R (Fin.castLE lt.le)
    have hp : Surjective p := funLeft_surjective_of_injective _ _ _ (Fin.castLE_injective lt.le)
    have : Injective p := .of_comp_right
      (Module.End.injective_of_surjective_fin (f := p ∘ₗ f) (hp.comp hf)) hf
    have ⟨⟨i, lt⟩, eq⟩ := injective_comp_right_iff_surjective.mp this ⟨n, lt⟩
    exact lt.ne congr($eq)
/-
**rankCondition_iff_le_of_comp_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rankCondition_iff_le_of_comp_eq_one : RankCondition R ↔ forall n m (f : (F
in n -> R) ->ₗ[R] Fin m -> R) (g : (Fin m -> R) ->ₗ[R] Fin n -> R), f ∘ₗ g = 1 -
> m <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `rankCondition_iff`：∀ (R : Type u) [inst : Semiring R],   RankCondition R
 ↔ ∀ {n m : ℕ} (f : (Fin n → R) →ₗ[R] Fin m → R), Function.Surjective ⇑f → m ≤ n
· 使用定理 `LinearMap.surjective_of_comp_eq_id`：surjective_of_comp_eq_id : Surjectiv
e g
· 使用定理 `Module.projective_lifting_property`：projective_lifting_property [h : Pro
jective R P] (f : M ->ₗ[R] N) (g : P ->ₗ[R] N) (hf : Function.Surjective f) : ex
ists h : P ->ₗ[R] M, f ∘…
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用定理 `Module.Free.function`：∀ (ι : Type u_1) (R : Type u_2) (M : Type u_3) [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [Fini
te ι] [Mod…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem rankCondition_iff_le_of_comp_eq_one : RankCondition R ↔ ∀ n m
    (f : (Fin n → R) →ₗ[R] Fin m → R) (g : (Fin m → R) →ₗ[R] Fin n → R), f ∘ₗ g = 1 → m ≤ n :=
  (rankCondition_iff R).trans ⟨fun h _ _ f _ eq ↦ h f (surjective_of_comp_eq_id _ _ eq),
    fun h _ _ _ hf ↦ have ⟨_, eq⟩ := Module.projective_lifting_property _ .id hf; h _ _ _ _ eq⟩
/-
**rankCondition_iff_matrix** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rankCondition_iff_matrix : RankCondition R ↔ forall n m (f : Matrix (Fin n
) (Fin m) R) (g : Matrix (Fin m) (Fin n) R), g * f = 1 -> m <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.forall_congr_right`：∀ {α : Sort u} {β : Sort v} {q : β → Prop} (e 
: α ≃ β), (∀ (a : α), q (e a)) ↔ ∀ (b : β), q b
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem rankCondition_iff_matrix : RankCondition R ↔ ∀ n m
    (f : Matrix (Fin n) (Fin m) R) (g : Matrix (Fin m) (Fin n) R), g * f = 1 → m ≤ n := by
  simp_rw [rankCondition_iff_le_of_comp_eq_one, ← toLinearMapRight'.toEquiv
    |>.forall_congr_right, LinearEquiv.coe_toEquiv, ← toLinearMapRight'_mul,
    Module.End.one_eq_id, ← toLinearMapRight'_one, toLinearMapRight'.injective.eq_iff]
/-
**invariantBasisNumber_iff_matrix** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：invariantBasisNumber_iff_matrix : InvariantBasisNumber R ↔ forall n m (f :
 Matrix (Fin n) (Fin m) R) (g : Matrix (Fin m) (Fin n) R), f * g = 1 -> g * f = 
1 -> n = m
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `invariantBasisNumber_iff`：∀ (R : Type u) [inst : Semiring R], InvariantB
asisNumber R ↔ ∀ {n m : ℕ} (a : (Fin n → R) ≃ₗ[R] Fin m → R), n = m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.self_trans_symm`：self_trans_symm (f : M₁ ≃ₛₗ[σ₁₂] M₂) : f.tr
ans f.symm = LinearEquiv.refl R₁ M₁
· 使用定理 `LinearMap.toMatrixRight'_id`：∀ {R : Type u_1} [inst : Semiring R] {m : T
ype u_3} [inst_1 : Fintype m] [inst_2 : DecidableEq m],   LinearMap.toMatrixRigh
t' LinearMap.id =…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearEquiv.symm_trans_self`：symm_trans_self (f : M₁ ≃ₛₗ[σ₁₂] M₂) : f.sy
mm.trans f = LinearEquiv.refl R₂ M₂
-/
theorem invariantBasisNumber_iff_matrix : InvariantBasisNumber R ↔ ∀ n m
    (f : Matrix (Fin n) (Fin m) R) (g : Matrix (Fin m) (Fin n) R), f * g = 1 → g * f = 1 → n = m :=
  (invariantBasisNumber_iff R).trans <| .intro (fun h n m f g hfg hgf ↦
      h (toLinearEquivRight'OfInv hfg hgf).symm) fun h n m e ↦ h n m (toMatrixRight' e)
    (toMatrixRight' e.symm) (by simp [← toMatrixRight'_comp]) (by simp [← toMatrixRight'_comp])

set_option backward.isDefEq.respectTransparency false in
/-- The rank condition is left-right symmetric. Note that the strong rank condition
is not left-right symmetric, see Remark (1.32) in §1.1D of [lam_1999]. -/
/-
**MulOpposite.rankCondition_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R], RankCondition Rᵐᵒᵖ ↔ RankCondition R
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.forall_congr_right`：∀ {α : Sort u} {β : Sort v} {q : β → Prop} (e 
: α ≃ β), (∀ (a : α), q (e a)) ↔ ∀ (b : β), q b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `AddEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst
_1 : Add N] (e : M ≃+ N), Function.Injective ⇑e
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.mapMatrix_apply`：∀ {m : Type u_2} {n : Type u_3} {α : Type u_11} {
β : Type u_12} (f : α ≃ β) (M : Matrix m n α), f.mapMatrix M = M.map ⇑f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MulOpposite.opEquiv_apply`：∀ {α : Type u_1}, ⇑MulOpposite.opEquiv = MulO
pposite.op
· 使用定理 `Matrix.mul_apply`：mul_apply [Fintype m] [Mul α] [AddCommMonoid α] {M : M
atrix l m α} {N : Matrix m n α} {i k} : (M * N) i k = ∑ j, M i j * N j k
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MulOpposite.opEquiv_symm_apply`：∀ {α : Type u_1}, ⇑MulOpposite.opEquiv.s
ymm = MulOpposite.unop
· 使用定理 `Finset.unop_sum`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid M
] (s : Finset ι) (f : ι → Mᵐᵒᵖ),   MulOpposite.unop (∑ x ∈ s, f x) = ∑ x ∈ s, Mu
lOppo…
· 使用定理 `Matrix.transposeAddEquiv_apply`：∀ (m : Type u_2) (n : Type u_3) (α : Typ
e u_11) [inst : Add α] (M : Matrix m n α),   (Matrix.transposeAddEquiv m n α) M 
= M.transpose
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.map_one`：∀ {n : Type u_3} {α : Type v} {β : Type w} [inst : Decid
ableEq n] [inst_1 : Zero α] [inst_2 : One α] [inst_3 : Zero β]   [inst_4 : One β
] (f…
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
The rank condition is left-right symmetric. Note that the strong rank condition
is not left-right symmetric, see Remark (1.32) in §1.1D of [lam_1999].
-/
protected theorem MulOpposite.rankCondition_iff : RankCondition Rᵐᵒᵖ ↔ RankCondition R := by
  simp_rw [rankCondition_iff_matrix, ← opEquiv.mapMatrix.forall_congr_right,
    ← opEquiv.mapMatrix.symm.injective.eq_iff]
  congr! 2 with n m
  refine forall_comm.trans <| .trans (forall_congr' ?_) (transposeAddEquiv ..).forall_congr_right
  refine fun f ↦ .trans (forall_congr' fun g ↦ ?_) (transposeAddEquiv ..).forall_congr_right
  rw [← (transposeAddEquiv ..).injective.eq_iff]
  congrm (?_ = ?_ → _)
  · ext; simp [map, mul_apply]
  · simp

set_option backward.isDefEq.respectTransparency false in
/-- Invariant basis number is left-right symmetric. -/
/-
**MulOpposite.invariantBasisNumber_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R], InvariantBasisNumber Rᵐᵒᵖ ↔ Invarian
tBasisNumber R
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.forall_congr_right`：∀ {α : Sort u} {β : Sort v} {q : β → Prop} (e 
: α ≃ β), (∀ (a : α), q (e a)) ↔ ∀ (b : β), q b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `AddEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst
_1 : Add N] (e : M ≃+ N), Function.Injective ⇑e
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.mapMatrix_apply`：∀ {m : Type u_2} {n : Type u_3} {α : Type u_11} {
β : Type u_12} (f : α ≃ β) (M : Matrix m n α), f.mapMatrix M = M.map ⇑f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MulOpposite.opEquiv_apply`：∀ {α : Type u_1}, ⇑MulOpposite.opEquiv = MulO
pposite.op
· 使用定理 `Matrix.mul_apply`：mul_apply [Fintype m] [Mul α] [AddCommMonoid α] {M : M
atrix l m α} {N : Matrix m n α} {i k} : (M * N) i k = ∑ j, M i j * N j k
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MulOpposite.opEquiv_symm_apply`：∀ {α : Type u_1}, ⇑MulOpposite.opEquiv.s
ymm = MulOpposite.unop
· 使用定理 `Finset.unop_sum`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid M
] (s : Finset ι) (f : ι → Mᵐᵒᵖ),   MulOpposite.unop (∑ x ∈ s, f x) = ∑ x ∈ s, Mu
lOppo…
· 使用定理 `Matrix.transposeAddEquiv_apply`：∀ (m : Type u_2) (n : Type u_3) (α : Typ
e u_11) [inst : Add α] (M : Matrix m n α),   (Matrix.transposeAddEquiv m n α) M 
= M.transpose
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.map_one`：∀ {n : Type u_3} {α : Type v} {β : Type w} [inst : Decid
ableEq n] [inst_1 : Zero α] [inst_2 : One α] [inst_3 : Zero β]   [inst_4 : One β
] (f…
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
Invariant basis number is left-right symmetric.
-/
protected theorem MulOpposite.invariantBasisNumber_iff :
    InvariantBasisNumber Rᵐᵒᵖ ↔ InvariantBasisNumber R := by
  simp_rw [invariantBasisNumber_iff_matrix, ← opEquiv.mapMatrix.forall_congr_right,
    ← opEquiv.mapMatrix.symm.injective.eq_iff]
  congr! 2 with n m
  refine forall_comm.trans <| .trans (forall_congr' ?_) (transposeAddEquiv ..).forall_congr_right
  refine fun f ↦ .trans (forall_congr' fun g ↦ ?_) (transposeAddEquiv ..).forall_congr_right
  rw [← (transposeAddEquiv ..).injective.eq_iff, ← (transposeAddEquiv (Fin m) ..).injective.eq_iff]
  congrm (?_ = ?_ → ?_ = ?_ → _)
  iterate 2 ext; simp [map, mul_apply]; simp
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [RankCondition R] : RankCondition Rᵐᵒᵖ := MulOpposite.rankCondition_iff.mpr ‹_›
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [InvariantBasisNumber R] : InvariantBasisNumber Rᵐᵒᵖ :=
  MulOpposite.invariantBasisNumber_iff.mpr ‹_›

end

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
variable {R : Type*} [Semiring R] [InvariantBasisNumber R]

/-
**Matrix.square_of_invertible** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.square_of_invertible (M : Matrix n m R) (N : Matrix m n R) (h : M *
 N = 1) (h' : N * M = 1) : Fintype.card n = Fintype.card m
参数：M : Matrix n m R；N : Matrix m n R；h : M * N = 1；h' : N * M = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `card_eq_of_linearEquiv`：card_eq_of_linearEquiv {α β : Type*} [Fintype α]
 [Fintype β] (f : (α -> R) ≃ₗ[R] β -> R) : Fintype.card α = Fintype.card β
-/
theorem Matrix.square_of_invertible (M : Matrix n m R) (N : Matrix m n R) (h : M * N = 1)
    (h' : N * M = 1) : Fintype.card n = Fintype.card m :=
  card_eq_of_linearEquiv R (Matrix.toLinearEquivRight'OfInv h' h)

open Function in
/-- Nontrivial commutative semirings `R` satisfy the rank condition.

If `R` is moreover a ring, then it satisfies the strong rank condition, see
`commRing_strongRankCondition`. It is unclear whether this generalizes to semirings. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Nontrivial commutative semirings `R` satisfy the rank condition.

If `R` is moreover a ring, then it satisfies the strong rank condition, see
`commRing_strongRankCondition`. It is unclear whether this generalizes to semiri
ngs.
-/
instance (priority := 100) rankCondition_of_nontrivial_of_commSemiring {R : Type*}
    [CommSemiring R] [Nontrivial R] : RankCondition R := inferInstance
