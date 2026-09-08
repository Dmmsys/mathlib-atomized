/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.LinearAlgebra.Alternating.Basic
public import Mathlib.LinearAlgebra.Multilinear.TensorProduct

/-!
# Exterior product of alternating maps

In this file we define `AlternatingMap.domCoprod`
to be the exterior product of two alternating maps,
taking values in the tensor product of the codomains of the original maps.
-/

@[expose] public section

open TensorProduct

variable {ιa ιb : Type*} [Fintype ιa] [Fintype ιb]
variable {R' : Type*} {Mᵢ N₁ N₂ : Type*} [CommSemiring R'] [AddCommGroup N₁] [Module R' N₁]
  [AddCommGroup N₂] [Module R' N₂] [AddCommMonoid Mᵢ] [Module R' Mᵢ]

namespace Equiv.Perm

/-- Elements which are considered equivalent if they differ only by swaps within α or β -/
/-
**Equiv.Perm.ModSumCongr** 是 Mathlib 中的一个缩写定义，位于命名空间 `Equiv.Perm`。
形式化陈述：ModSumCongr (α β : Type*)
参数：α β : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Elements which are considered equivalent if they differ only by swaps within α o
r β
-/
abbrev ModSumCongr (α β : Type*) :=
  _ ⧸ (Equiv.Perm.sumCongrHom α β).range

end Equiv.Perm

namespace AlternatingMap

open Equiv

variable [DecidableEq ιa] [DecidableEq ιb]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- summand used in `AlternatingMap.domCoprod` -/
/-
**AlternatingMap.domCoprod.summand** 是 Mathlib 中的一个定义，位于命名空间 `AlternatingMap.dom
Coprod`。
形式化陈述：{ιa : Type u_1} →   {ιb : Type u_2} →     [Fintype ιa] →       [Fintype ιb
] →         {R' : Type u_3} →           {Mᵢ : Type u_4} →             {N₁ : Type
 u_5} →               {N₂ : Type u_6} →                 [inst : CommSemiring R']
 →                   [inst_1 : AddCommGroup N₁] →                     [inst_2 : 
_root_.Module R' N₁] →                       [inst_3 : AddCommGroup N₂] →       
                  [inst_4 : _root_.Module R' N₂] →                           [in
st_5 : AddCommMonoid Mᵢ] →                             [inst_6 : _root_.Module R
' Mᵢ] →                               [DecidableEq ιa] →                        
         [DecidableEq ιb] →                                   Mᵢ [⋀^ιa]→ₗ[R'] N₁
 →                                     Mᵢ [⋀^ιb]→ₗ[R'] N₂ →                     
                  Equiv.Perm.ModSumCongr ιa ιb →                                
         MultilinearMap R' (fun x => Mᵢ) (TensorProduct R' N₁ N₂)
参数：fun x => Mᵢ；TensorProduct R' N₁ N₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
summand used in `AlternatingMap.domCoprod`
-/
def domCoprod.summand (a : Mᵢ [⋀^ιa]→ₗ[R'] N₁) (b : Mᵢ [⋀^ιb]→ₗ[R'] N₂)
    (σ : Perm.ModSumCongr ιa ιb) : MultilinearMap R' (fun _ : ιa ⊕ ιb => Mᵢ) (N₁ ⊗[R'] N₂) :=
  Quotient.liftOn' σ
    (fun σ =>
      Equiv.Perm.sign σ •
        (MultilinearMap.domCoprod ↑a ↑b : MultilinearMap R' (fun _ => Mᵢ) (N₁ ⊗ N₂)).domDomCongr σ)
    fun σ₁ σ₂ H => by
    rw [QuotientGroup.leftRel_apply] at H
    obtain ⟨⟨sl, sr⟩, h⟩ := H
    ext v
    simp only [MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply,
      coe_multilinearMap, _root_.smul_apply]
    replace h := inv_mul_eq_iff_eq_mul.mp h.symm
    have : Equiv.Perm.sign (σ₁ * Perm.sumCongrHom _ _ (sl, sr))
      = Equiv.Perm.sign σ₁ * (Equiv.Perm.sign sl * Equiv.Perm.sign sr) := by simp
    rw [h, this, mul_smul, mul_smul, smul_left_cancel_iff, ← TensorProduct.tmul_smul,
      TensorProduct.smul_tmul', a.map_congr_perm _ sl, b.map_congr_perm _ sr]
    simp only [Sum.map_inr, Perm.sumCongrHom_apply, Perm.sumCongr_apply, Sum.map_inl,
      Function.comp_def, Perm.coe_mul]
/-
**AlternatingMap.domCoprod.summand_mk''** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMa
p.domCoprod`。
形式化陈述：∀ {ιa : Type u_1} {ιb : Type u_2} [inst : Fintype ιa] [inst_1 : Fintype ιb
] {R' : Type u_3} {Mᵢ : Type u_4}   {N₁ : Type u_5} {N₂ : Type u_6} [inst_2 : Co
mmSemiring R'] [inst_3 : AddCommGroup N₁] [inst_4 : _root_.Module R' N₁]   [inst
_5 : AddCommGroup N₂] [inst_6 : _root_.Module R' N₂] [inst_7 : AddCommMonoid Mᵢ]
 [inst_8 : _root_.Module R' Mᵢ]   [inst_9 : DecidableEq ιa] [inst_10 : Decidable
Eq ιb] (a : Mᵢ [⋀^ιa]→ₗ[R'] N₁) (b : Mᵢ [⋀^ιb]→ₗ[R'] N₂)   (σ : Equiv.Perm (ιa ⊕
 ιb)),   AlternatingMap.domCoprod.summand a b (Quotient.mk'' σ) =     Equiv.Perm
.sign σ • MultilinearMap.domDomCongr σ ((↑a).domCoprod ↑b)
参数：a : Mᵢ [⋀^ιa]→ₗ[R'] N₁；b : Mᵢ [⋀^ιb]→ₗ[R'] N₂；σ : Equiv.Perm (ιa ⊕ ιb)；Quotie
nt.mk'' σ；(↑a).domCoprod ↑b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
-/
theorem domCoprod.summand_mk'' (a : Mᵢ [⋀^ιa]→ₗ[R'] N₁) (b : Mᵢ [⋀^ιb]→ₗ[R'] N₂)
    (σ : Equiv.Perm (ιa ⊕ ιb)) :
    domCoprod.summand a b (Quotient.mk'' σ) =
      Equiv.Perm.sign σ •
        (MultilinearMap.domCoprod ↑a ↑b : MultilinearMap R' (fun _ => Mᵢ) (N₁ ⊗ N₂)).domDomCongr
          σ :=
  rfl

/-- Swapping elements in `σ` with equal values in `v` results in an addition that cancels -/
/-
**AlternatingMap.domCoprod.summand_add_swap_smul_eq_zero** 是 Mathlib 中的一个定理，位于命名
空间 `AlternatingMap.domCoprod`。
形式化陈述：∀ {ιa : Type u_1} {ιb : Type u_2} [inst : Fintype ιa] [inst_1 : Fintype ιb
] {R' : Type u_3} {Mᵢ : Type u_4}   {N₁ : Type u_5} {N₂ : Type u_6} [inst_2 : Co
mmSemiring R'] [inst_3 : AddCommGroup N₁] [inst_4 : _root_.Module R' N₁]   [inst
_5 : AddCommGroup N₂] [inst_6 : _root_.Module R' N₂] [inst_7 : AddCommMonoid Mᵢ]
 [inst_8 : _root_.Module R' Mᵢ]   [inst_9 : DecidableEq ιa] [inst_10 : Decidable
Eq ιb] (a : Mᵢ [⋀^ιa]→ₗ[R'] N₁) (b : Mᵢ [⋀^ιb]→ₗ[R'] N₂)   (σ : Equiv.Perm.ModSu
mCongr ιa ιb) {v : ιa ⊕ ιb → Mᵢ} {i j : ιa ⊕ ιb},   v i = v j →     i ≠ j →     
  (AlternatingMap.domCoprod.summand a b σ) v + (AlternatingMap.domCoprod.summand
 a b (Equiv.swap i j • σ)) v = 0
参数：a : Mᵢ [⋀^ιa]→ₗ[R'] N₁；b : Mᵢ [⋀^ιb]→ₗ[R'] N₂；σ : Equiv.Perm.ModSumCongr ιa ι
b；AlternatingMap.domCoprod.summand a b σ；AlternatingMap.domCoprod.summand a b (E
quiv.swap i j • σ)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Equiv.Perm.sign_mul`：sign_mul (f g : Perm α) : sign (f * g) = sign f * s
ign g
· 使用定理 `Equiv.Perm.sign_swap`：sign_swap {x y : α} (h : x != y) : sign (swap x y)
 = -1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `MultilinearMap.instIsSMulApplyForall`：∀ {R : Type uR} {S : Type uS} {ι :
 Type uι} {M₁ : ι → Type v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i :
 ι) → AddCommMonoid (M₁ i)…
· 使用定理 `MultilinearMap.domDomCongr_apply`：∀ {R : Type uR} {M₂ : Type v₂} {M₃ : T
ype v₃} [inst : Semiring R] [inst_1 : AddCommMonoid M₂]   [inst_2 : AddCommMonoi
d M₃] [inst_3 : _root_…
· 使用定理 `MultilinearMap.domCoprod_apply`：∀ {R : Type u_1} {ι₁ : Type u_2} {ι₂ : T
ype u_3} [inst : CommSemiring R] {N₁ : Type u_6} [inst_1 : AddCommMonoid N₁]   [
inst_2 : _root_.Modu…
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Units.neg_smul`：Units.neg_smul [Ring R] [AddCommGroup M] [Module R M] (u
 : Rˣ) (x : M) : -u • x = -(u • x)
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `MultilinearMap.instIsNegApplyForall`：∀ {R : Type uR} {ι : Type uι} {M₁ :
 ι → Type v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMo
noid (M₁ i)] [inst_2 : Ad…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.apply_swap_eq_self`：apply_swap_eq_self {v : α -> β} {i j : α} (hv 
: v i = v j) (k : α) : v (swap i j k) = v k
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0

--- 原说明 ---
Swapping elements in `σ` with equal values in `v` results in an addition that ca
ncels
-/
theorem domCoprod.summand_add_swap_smul_eq_zero (a : Mᵢ [⋀^ιa]→ₗ[R'] N₁)
    (b : Mᵢ [⋀^ιb]→ₗ[R'] N₂) (σ : Perm.ModSumCongr ιa ιb) {v : ιa ⊕ ιb → Mᵢ}
    {i j : ιa ⊕ ιb} (hv : v i = v j) (hij : i ≠ j) :
    domCoprod.summand a b σ v + domCoprod.summand a b (swap i j • σ) v = 0 := by
  induction σ using Quotient.inductionOn'
  dsimp only [Quotient.liftOn'_mk'', Quotient.map'_mk'', MulAction.Quotient.smul_mk,
    domCoprod.summand]
  rw [smul_eq_mul, Perm.sign_mul, Perm.sign_swap hij]
  simp only [one_mul, neg_mul, Function.comp_apply, Units.neg_smul, Perm.coe_mul,
    _root_.smul_apply, _root_.neg_apply, MultilinearMap.domDomCongr_apply,
    MultilinearMap.domCoprod_apply]
  convert! add_neg_cancel (G := N₁ ⊗[R'] N₂) _ using 6 <;>
    · ext k
      rw [Equiv.apply_swap_eq_self hv]

/-- Swapping elements in `σ` with equal values in `v` result in zero if the swap has no effect
on the quotient. -/
/-
**AlternatingMap.domCoprod.summand_eq_zero_of_smul_invariant** 是 Mathlib 中的一个定理，
位于命名空间 `AlternatingMap.domCoprod`。
形式化陈述：∀ {ιa : Type u_1} {ιb : Type u_2} [inst : Fintype ιa] [inst_1 : Fintype ιb
] {R' : Type u_3} {Mᵢ : Type u_4}   {N₁ : Type u_5} {N₂ : Type u_6} [inst_2 : Co
mmSemiring R'] [inst_3 : AddCommGroup N₁] [inst_4 : _root_.Module R' N₁]   [inst
_5 : AddCommGroup N₂] [inst_6 : _root_.Module R' N₂] [inst_7 : AddCommMonoid Mᵢ]
 [inst_8 : _root_.Module R' Mᵢ]   [inst_9 : DecidableEq ιa] [inst_10 : Decidable
Eq ιb] (a : Mᵢ [⋀^ιa]→ₗ[R'] N₁) (b : Mᵢ [⋀^ιb]→ₗ[R'] N₂)   (σ : Equiv.Perm.ModSu
mCongr ιa ιb) {v : ιa ⊕ ιb → Mᵢ} {i j : ιa ⊕ ιb},   v i = v j → i ≠ j → Equiv.sw
ap i j • σ = σ → (AlternatingMap.domCoprod.summand a b σ) v = 0
参数：a : Mᵢ [⋀^ιa]→ₗ[R'] N₁；b : Mᵢ [⋀^ιb]→ₗ[R'] N₂；σ : Equiv.Perm.ModSumCongr ιa ι
b；AlternatingMap.domCoprod.summand a b σ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `QuotientGroup.leftRel_apply`：leftRel_apply {x y : α} : leftRel s x y ↔ x
⁻¹ * y in s
· 使用定理 `Quotient.exact'`：exact' {a b : α} : (Quotient.mk'' a : Quotient s₁) = Qu
otient.mk'' b -> s₁ a b
· 使用定理 `AlternatingMap.map_eq_zero_of_eq`：map_eq_zero_of_eq (v : ι -> M) {i j : 
ι} (h : v i = v j) (hij : i != j) : f v = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `MultilinearMap.instIsSMulApplyForall`：∀ {R : Type uR} {S : Type uS} {ι :
 Type uι} {M₁ : ι → Type v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i :
 ι) → AddCommMonoid (M₁ i)…
· 使用定理 `MultilinearMap.domDomCongr_apply`：∀ {R : Type uR} {M₂ : Type v₂} {M₃ : T
ype v₃} [inst : Semiring R] [inst_1 : AddCommMonoid M₂]   [inst_2 : AddCommMonoi
d M₃] [inst_3 : _root_…
· 使用定理 `MultilinearMap.domCoprod_apply`：∀ {R : Type u_1} {ι₁ : Type u_2} {ι₂ : T
ype u_3} [inst : CommSemiring R] {N₁ : Type u_6} [inst_1 : AddCommMonoid N₁]   [
inst_2 : _root_.Modu…
· 使用定理 `TensorProduct.zero_tmul`：zero_tmul (n : N) : (0 : M) otimesₜ[R] n = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.inv_eq_iff_eq`：inv_eq_iff_eq {f : Perm α} {x y : α} : f⁻¹ x =
 y ↔ x = f y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.Perm.sumCongrHom_apply`：∀ (α : Type u_7) (β : Type u_8) (a : Equiv
.Perm α × Equiv.Perm β), (Equiv.Perm.sumCongrHom α β) a = a.1.sumCongr a.2
· 使用定理 `Equiv.sumCongr_apply`：∀ {α₁ : Type u_9} {α₂ : Type u_10} {β₁ : Type u_11
} {β₂ : Type u_12} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) (a : α₁ ⊕ β₁),   (ea.sumCongr e
b) a = Sum…
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.swap_apply_left`：swap_apply_left (a b : α) : swap a b a = b
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Equiv.congr_fun`：∀ {α : Sort u} {β : Sort v} {f g : α ≃ β}, f = g → ∀ (x
 : α), f x = g x
· 使用定理 `TensorProduct.tmul_zero`：tmul_zero (m : M) : m otimesₜ[R] (0 : N) = 0

--- 原说明 ---
Swapping elements in `σ` with equal values in `v` result in zero if the swap has
 no effect
on the quotient.
-/
theorem domCoprod.summand_eq_zero_of_smul_invariant (a : Mᵢ [⋀^ιa]→ₗ[R'] N₁)
    (b : Mᵢ [⋀^ιb]→ₗ[R'] N₂) (σ : Perm.ModSumCongr ιa ιb) {v : ιa ⊕ ιb → Mᵢ}
    {i j : ιa ⊕ ιb} (hv : v i = v j) (hij : i ≠ j) :
    swap i j • σ = σ → domCoprod.summand a b σ v = 0 := by
  induction σ using Quotient.inductionOn' with | _ σ
  dsimp only [Quotient.liftOn'_mk'', Quotient.map'_mk'', _root_.smul_apply,
    MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply, domCoprod.summand]
  intro hσ
  obtain ⟨⟨sl, sr⟩, hσ⟩ := QuotientGroup.leftRel_apply.mp (Quotient.exact' hσ)
  rcases hi : σ⁻¹ i with i' | i' <;> rcases hj : σ⁻¹ j with j' | j' <;>
    rw [Perm.inv_eq_iff_eq] at hi hj <;> subst hi hj
  -- the term pairs with and cancels another term
  case inl.inr => simpa using Equiv.congr_fun hσ (Sum.inl i')
  case inr.inl => simpa using Equiv.congr_fun hσ (Sum.inr i')
  -- the term does not pair but is zero
  case inl.inl =>
    suffices (a fun i ↦ v (σ (Sum.inl i))) = 0 by simp_all
    exact AlternatingMap.map_eq_zero_of_eq _ _ hv fun hij' => hij (hij' ▸ rfl)
  case inr.inr =>
    suffices (b fun i ↦ v (σ (Sum.inr i))) = 0 by simp_all
    exact b.map_eq_zero_of_eq _ hv fun hij' => hij (hij' ▸ rfl)

/-- Like `MultilinearMap.domCoprod`, but ensures the result is also alternating.

Note that this is usually defined (for instance, as used in Proposition 22.24 in [Gallier2011Notes])
over integer indices `ιa = Fin n` and `ιb = Fin m`, as
$$
(f \wedge g)(u_1, \ldots, u_{m+n}) =
  \sum_{\operatorname{shuffle}(m, n)} \operatorname{sign}(\sigma)
    f(u_{\sigma(1)}, \ldots, u_{\sigma(m)}) g(u_{\sigma(m+1)}, \ldots, u_{\sigma(m+n)}),
$$
where $\operatorname{shuffle}(m, n)$ consists of all permutations of $[1, m+n]$ such that
$\sigma(1) < \cdots < \sigma(m)$ and $\sigma(m+1) < \cdots < \sigma(m+n)$.

Here, we generalize this by replacing:
* the product in the sum with a tensor product
* the filtering of $[1, m+n]$ to shuffles with an isomorphic quotient
* the additions in the subscripts of $\sigma$ with an index of type `Sum`

The specialized version can be obtained by combining this definition with `finSumFinEquiv` and
`LinearMap.mul'`.
-/
@[simps]
/-
**AlternatingMap.domCoprod** 是 Mathlib 中的一个定义，位于命名空间 `AlternatingMap`。
形式化陈述：domCoprod (a : Mᵢ [⋀^ιa]->ₗ[R'] N₁) (b : Mᵢ [⋀^ιb]->ₗ[R'] N₂) : Mᵢ [⋀^ιa o
plus ιb]->ₗ[R'] (N₁ otimes[R'] N₂)
参数：a : Mᵢ [⋀^ιa]->ₗ[R'] N₁；b : Mᵢ [⋀^ιb]->ₗ[R'] N₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Like `MultilinearMap.domCoprod`, but ensures the result is also alternating.

Note that this is usually defined (for instance, as used in Proposition 22.24 in
 [Gallier2011Notes])
over integer indices `ιa = Fin n` and `ιb = Fin m`, as
$$
(f \wedge g)(u_1, \ldots, u_{m+n}) =
  \sum_{\operatorname{shuffle}(m, n)} \operatorname{sign}(\sigma)
    f(u_{\sigma(1)}, \ldots, u_{\sigma(m)}) g(u_{\sigma(m+1)}, \ldots, u_{\sigma
(m+n)}),
$$
where $\operatorname{shuffle}(m, n)$ consists of all permutations of $[1, m+n]$ 
such that
$\sigma(1) < \cdots < \sigma(m)$ and $\sigma(m+1) < \cdots < \sigma(m+n)$.

Here, we generalize this by replacing:
* the product in the sum with a tensor product
* the filtering of $[1, m+n]$ to shuffles with an isomorphic quotient
* the additions in the subscripts of $\sigma$ with an index of type `Sum`

The specialized version can be obtained by combining this definition with `finSu
mFinEquiv` and
`LinearMap.mul'`.
-/
def domCoprod (a : Mᵢ [⋀^ιa]→ₗ[R'] N₁) (b : Mᵢ [⋀^ιb]→ₗ[R'] N₂) :
    Mᵢ [⋀^ιa ⊕ ιb]→ₗ[R'] (N₁ ⊗[R'] N₂) :=
  { ∑ σ : Perm.ModSumCongr ιa ιb, domCoprod.summand a b σ with
    toFun := fun v => (⇑(∑ σ : Perm.ModSumCongr ιa ιb, domCoprod.summand a b σ)) v
    map_eq_zero_of_eq' := fun v i j hv hij => by
      rw [_root_.sum_apply]
      exact
        Finset.sum_involution (fun σ _ => Equiv.swap i j • σ)
          (fun σ _ => domCoprod.summand_add_swap_smul_eq_zero a b σ hv hij)
          (fun σ _ => mt <| domCoprod.summand_eq_zero_of_smul_invariant a b σ hv hij)
          (fun σ _ => Finset.mem_univ _) fun σ _ =>
          Equiv.swap_smul_involutive i j σ }
/-
**AlternatingMap.domCoprod_coe** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：domCoprod_coe (a : Mᵢ [⋀^ιa]->ₗ[R'] N₁) (b : Mᵢ [⋀^ιb]->ₗ[R'] N₂) : (↑(a.d
omCoprod b) : MultilinearMap R' (fun _ => Mᵢ) _) = ∑ σ : Perm.ModSumCongr ιa ιb,
 domCoprod.summand a b σ
参数：a : Mᵢ [⋀^ιa]->ₗ[R'] N₁；b : Mᵢ [⋀^ιb]->ₗ[R'] N₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
-/
theorem domCoprod_coe (a : Mᵢ [⋀^ιa]→ₗ[R'] N₁) (b : Mᵢ [⋀^ιb]→ₗ[R'] N₂) :
    (↑(a.domCoprod b) : MultilinearMap R' (fun _ => Mᵢ) _) =
      ∑ σ : Perm.ModSumCongr ιa ιb, domCoprod.summand a b σ :=
  MultilinearMap.ext fun _ => rfl

/-- A more bundled version of `AlternatingMap.domCoprod` that maps
`((ι₁ → N) → N₁) ⊗ ((ι₂ → N) → N₂)` to `(ι₁ ⊕ ι₂ → N) → N₁ ⊗ N₂`. -/
/-
**AlternatingMap.domCoprod'** 是 Mathlib 中的一个定义，位于命名空间 `AlternatingMap`。
形式化陈述：domCoprod' : (Mᵢ [⋀^ιa]->ₗ[R'] N₁) otimes[R'] (Mᵢ [⋀^ιb]->ₗ[R'] N₂) ->ₗ[R'
] (Mᵢ [⋀^ιa oplus ιb]->ₗ[R'] (N₁ otimes[R'] N₂))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A more bundled version of `AlternatingMap.domCoprod` that maps
`((ι₁ → N) → N₁) ⊗ ((ι₂ → N) → N₂)` to `(ι₁ ⊕ ι₂ → N) → N₁ ⊗ N₂`.
-/
def domCoprod' :
    (Mᵢ [⋀^ιa]→ₗ[R'] N₁) ⊗[R'] (Mᵢ [⋀^ιb]→ₗ[R'] N₂) →ₗ[R']
      (Mᵢ [⋀^ιa ⊕ ιb]→ₗ[R'] (N₁ ⊗[R'] N₂)) :=
  TensorProduct.lift <| by
    refine
      LinearMap.mk₂ R' domCoprod (fun m₁ m₂ n => ?_) (fun c m n => ?_) (fun m n₁ n₂ => ?_)
        fun c m n => ?_ <;>
    · ext
      simp only [domCoprod_apply, add_apply, smul_apply, ← Finset.sum_add_distrib,
        Finset.smul_sum, _root_.sum_apply, domCoprod.summand]
      congr
      ext σ
      induction σ using Quotient.inductionOn'
      simp only [Quotient.liftOn'_mk'', coe_add, coe_smul, _root_.smul_apply,
        ← MultilinearMap.domCoprod'_apply]
      simp only [TensorProduct.add_tmul, ← TensorProduct.smul_tmul', TensorProduct.tmul_add,
        TensorProduct.tmul_smul, map_add, map_smul]
      first | rw [← smul_add] | rw [smul_comm]
      rfl

@[simp]
/-
**AlternatingMap.domCoprod'_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：∀ {ιa : Type u_1} {ιb : Type u_2} [inst : Fintype ιa] [inst_1 : Fintype ιb
] {R' : Type u_3} {Mᵢ : Type u_4}   {N₁ : Type u_5} {N₂ : Type u_6} [inst_2 : Co
mmSemiring R'] [inst_3 : AddCommGroup N₁] [inst_4 : _root_.Module R' N₁]   [inst
_5 : AddCommGroup N₂] [inst_6 : _root_.Module R' N₂] [inst_7 : AddCommMonoid Mᵢ]
 [inst_8 : _root_.Module R' Mᵢ]   [inst_9 : DecidableEq ιa] [inst_10 : Decidable
Eq ιb] (a : Mᵢ [⋀^ιa]→ₗ[R'] N₁) (b : Mᵢ [⋀^ιb]→ₗ[R'] N₂),   AlternatingMap.domCo
prod' (a ⊗ₜ[R'] b) = a.domCoprod b
参数：a : Mᵢ [⋀^ιa]→ₗ[R'] N₁；b : Mᵢ [⋀^ιb]→ₗ[R'] N₂；a ⊗ₜ[R'] b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem domCoprod'_apply (a : Mᵢ [⋀^ιa]→ₗ[R'] N₁) (b : Mᵢ [⋀^ιb]→ₗ[R'] N₂) :
    domCoprod' (a ⊗ₜ[R'] b) = domCoprod a b :=
  rfl

end AlternatingMap

open Equiv

/-- A helper lemma for `MultilinearMap.domCoprod_alternization`. -/
/-
**MultilinearMap.domCoprod_alternization_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MultilinearMap.domCoprod_alternization_coe [DecidableEq ιa] [DecidableEq ι
b] (a : MultilinearMap R' (fun _ : ιa => Mᵢ) N₁) (b : MultilinearMap R' (fun _ :
 ιb => Mᵢ) N₂) : MultilinearMap.domCoprod (MultilinearMap.alternatization a) (Mu
ltilinearMap.alternatization b) = ∑ σa : Perm ιa, ∑ σb : Perm ιb, Equiv.Perm.sig
n σa • Equiv.Perm.sign σb • MultilinearMap.domCoprod (a.domDomCongr σa) (b.domDo
mCongr σb)
参数：a : MultilinearMap R' (fun _ : ιa => Mᵢ) N₁；b : MultilinearMap R' (fun _ : ιb
 => Mᵢ) N₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MultilinearMap.alternatization_coe`：alternatization_coe (m : Multilinear
Map R (fun _ : ι => M) N') : ↑(alternatization m) = (∑ σ : Perm ι, Equiv.Perm.si
gn σ • m.domDomCongr σ :…
· 使用定理 `TensorProduct.sum_tmul`：sum_tmul {α : Type*} (s : Finset α) (m : α -> M)
 (n : N) : (∑ a in s, m a) otimesₜ[R] n = ∑ a in s, m a otimesₜ[R] n
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `TensorProduct.tmul_sum`：tmul_sum (m : M) {α : Type*} (s : Finset α) (n :
 α -> N) : (m otimesₜ[R] ∑ a in s, n a) = ∑ a in s, m otimesₜ[R] n a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `TensorProduct.tmul_smul`：tmul_smul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (x : M) (y : N) : x otimesₜ (r • y) = r • x otimesₜ[R] y
· 使用定理 `TensorProduct.CompatibleSMul.unit`：∀ {R : Type u_1} [inst : CommSemiring
 R] {M : Type u_2} {N : Type u_3} [inst_1 : AddCommGroup M]   [inst_2 : AddCommM
onoid N] [inst_3 : _roo…
· 使用定理 `TensorProduct.CompatibleSMul.int`：∀ {R : Type u_1} [inst : CommSemiring 
R] {M : Type u_2} {P : Type u_4} [inst_1 : AddCommGroup M]   [inst_2 : AddCommGr
oup P] [inst_3 : _root…

--- 原说明 ---
A helper lemma for `MultilinearMap.domCoprod_alternization`.
-/
theorem MultilinearMap.domCoprod_alternization_coe [DecidableEq ιa] [DecidableEq ιb]
    (a : MultilinearMap R' (fun _ : ιa => Mᵢ) N₁) (b : MultilinearMap R' (fun _ : ιb => Mᵢ) N₂) :
    MultilinearMap.domCoprod (MultilinearMap.alternatization a)
      (MultilinearMap.alternatization b) =
      ∑ σa : Perm ιa, ∑ σb : Perm ιb,
        Equiv.Perm.sign σa • Equiv.Perm.sign σb •
          MultilinearMap.domCoprod (a.domDomCongr σa) (b.domDomCongr σb) := by
  simp_rw [← MultilinearMap.domCoprod'_apply, MultilinearMap.alternatization_coe]
  simp_rw [TensorProduct.sum_tmul, TensorProduct.tmul_sum, _root_.map_sum,
    ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  rfl

open AlternatingMap

set_option backward.isDefEq.respectTransparency.types false in
open Perm in
/-- Computing the `MultilinearMap.alternatization` of the `MultilinearMap.domCoprod` is the same
as computing the `AlternatingMap.domCoprod` of the `MultilinearMap.alternatization`s.
-/
/-
**MultilinearMap.domCoprod_alternization** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MultilinearMap.domCoprod_alternization [DecidableEq ιa] [DecidableEq ιb] (
a : MultilinearMap R' (fun _ : ιa => Mᵢ) N₁) (b : MultilinearMap R' (fun _ : ιb 
=> Mᵢ) N₂) : MultilinearMap.alternatization (MultilinearMap.domCoprod a b) = a.a
lternatization.domCoprod (MultilinearMap.alternatization b)
参数：a : MultilinearMap R' (fun _ : ιa => Mᵢ) N₁；b : MultilinearMap R' (fun _ : ιb
 => Mᵢ) N₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.coe_multilinearMap_injective`：coe_multilinearMap_injectiv
e : Function.Injective ((↑) : M [⋀^ι]->ₗ[R] N -> MultilinearMap R (fun _ : ι => 
M) N)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlternatingMap.domCoprod_coe`：domCoprod_coe (a : Mᵢ [⋀^ιa]->ₗ[R'] N₁) (b
 : Mᵢ [⋀^ιb]->ₗ[R'] N₂) : (↑(a.domCoprod b) : MultilinearMap R' (fun _ => Mᵢ) _)
 = ∑ σ : Perm.ModS…
· 使用定理 `MultilinearMap.alternatization_coe`：alternatization_coe (m : Multilinear
Map R (fun _ : ι => M) N') : ↑(alternatization m) = (∑ σ : Perm ι, Equiv.Perm.si
gn σ • m.domDomCongr σ :…
· 使用定理 `Finset.sum_partition`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [in
st : AddCommMonoid M] {f : ι → M} (R : Setoid ι)   [inst_1 : DecidableRel ⇑R], ∑
 x ∈ s, f …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.Perm.sumCongrHom_apply`：∀ (α : Type u_7) (β : Type u_8) (a : Equiv
.Perm α × Equiv.Perm β), (Equiv.Perm.sumCongrHom α β) a = a.1.sumCongr a.2
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.map_univ_equiv`：map_univ_equiv [Fintype β] (f : β ≃ α) : univ.map
 f.toEmbedding = univ
· 使用定理 `Finset.filter_map`：filter_map {p : β -> Prop} [DecidablePred p] : (s.map
 f).filter p = (s.filter (p ∘ f)).map f
· 使用定理 `Finset.sum_map`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : A
ddCommMonoid M] (s : Finset ι) (e : ι ↪ κ) (f : κ → M),   ∑ x ∈ Finset.map e s, 
f x …
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `Equiv.Perm.sign_mul`：sign_mul (f g : Perm α) : sign (f * g) = sign f * s
ign g
· 使用定理 `Finset.univ_filter_exists`：univ_filter_exists (f : α -> β) [Fintype β] [
DecidablePred fun y => exists x, f x = y] [DecidableEq β] : (Finset.univ.filter 
fun y => exists…
· 使用定理 `Finset.sum_image`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_4} [inst :
 AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι]   {s : Finset κ} {g : κ →
 ι}, S…
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Equiv.Perm.sumCongrHom_injective`：sumCongrHom_injective {α β : Type*} : 
Function.Injective (sumCongrHom α β)
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
Computing the `MultilinearMap.alternatization` of the `MultilinearMap.domCoprod`
 is the same
as computing the `AlternatingMap.domCoprod` of the `MultilinearMap.alternatizati
on`s.
-/
theorem MultilinearMap.domCoprod_alternization [DecidableEq ιa] [DecidableEq ιb]
    (a : MultilinearMap R' (fun _ : ιa => Mᵢ) N₁) (b : MultilinearMap R' (fun _ : ιb => Mᵢ) N₂) :
    MultilinearMap.alternatization (MultilinearMap.domCoprod a b) =
      a.alternatization.domCoprod (MultilinearMap.alternatization b) := by
  apply coe_multilinearMap_injective
  rw [domCoprod_coe, MultilinearMap.alternatization_coe,
    Finset.sum_partition (QuotientGroup.leftRel (Perm.sumCongrHom ιa ιb).range)]
  congr 1
  ext1 σ
  induction σ using Quotient.inductionOn' with
  | h σ =>
  set f := sumCongrHom ιa ιb
  calc
    ∑ τ ∈ _, sign τ • domDomCongr τ (a.domCoprod b) =
        ∑ τ ∈ {τ | τ⁻¹ * σ ∈ f.range}, sign τ • domDomCongr τ (a.domCoprod b) := by
      simp [QuotientGroup.leftRel_apply, f, Quotient.eq]
    _ = ∑ τ ∈ {τ | τ⁻¹ ∈ f.range}, sign (σ * τ) • domDomCongr (σ * τ) (a.domCoprod b) := by
      conv_lhs => rw [← Finset.map_univ_equiv (Equiv.mulLeft σ), Finset.filter_map, Finset.sum_map]
      simp [-MonoidHom.mem_range]
    _ = ∑ τ, sign (σ * f τ) • domDomCongr (σ * f τ) (a.domCoprod b) := by
      simp_rw [f, Subgroup.inv_mem_iff, MonoidHom.mem_range, Finset.univ_filter_exists,
        Finset.sum_image sumCongrHom_injective.injOn]
    _ = ∑ τ : Perm ιa × Perm ιb,
         sign σ • (domDomCongrEquiv σ) (sign τ.1 • sign τ.2 •
           (domDomCongr τ.1 a).domCoprod (domDomCongr τ.2 b)) := by
      simp [f, domDomCongr_mul, domCoprod_domDomCongr_sumCongr, mul_smul]
    _ = domCoprod.summand (alternatization a) (alternatization b) (Quotient.mk'' σ) := by
      simp [domCoprod.summand_mk'', domCoprod_alternization_coe, ← domDomCongrEquiv_apply,
        Finset.smul_sum, ← Finset.sum_product']

/-- Taking the `MultilinearMap.alternatization` of the `MultilinearMap.domCoprod` of two
`AlternatingMap`s gives a scaled version of the `AlternatingMap.coprod` of those maps.
-/
/-
**MultilinearMap.domCoprod_alternization_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MultilinearMap.domCoprod_alternization_eq [DecidableEq ιa] [DecidableEq ιb
] (a : Mᵢ [⋀^ιa]->ₗ[R'] N₁) (b : Mᵢ [⋀^ιb]->ₗ[R'] N₂) : MultilinearMap.alternati
zation (MultilinearMap.domCoprod a b : MultilinearMap R' (fun _ : ιa oplus ιb =>
 Mᵢ) (N₁ otimes N₂)) = ((Fintype.card ιa).factorial * (Fintype.card ιb).factoria
l) • a.domCoprod b
参数：a : Mᵢ [⋀^ιa]->ₗ[R'] N₁；b : Mᵢ [⋀^ιb]->ₗ[R'] N₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MultilinearMap.domCoprod_alternization`：MultilinearMap.domCoprod_alterni
zation [DecidableEq ιa] [DecidableEq ιb] (a : MultilinearMap R' (fun _ : ιa => M
ᵢ) N₁) (b : MultilinearMap R…
· 使用定理 `AlternatingMap.coe_alternatization`：coe_alternatization [DecidableEq ι] 
[Fintype ι] (a : M [⋀^ι]->ₗ[R] N') : MultilinearMap.alternatization (a : Multili
nearMap R (fun _ => M) N…
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlternatingMap.domCoprod'_apply`：∀ {ιa : Type u_1} {ιb : Type u_2} [inst
 : Fintype ιa] [inst_1 : Fintype ιb] {R' : Type u_3} {Mᵢ : Type u_4}   {N₁ : Typ
e u_5} {N₂ : Type u_6…
· 使用定理 `TensorProduct.smul_tmul'`：smul_tmul' (r : R') (m : M) (n : N) : r • m ot
imesₜ[R] n = (r • m) otimesₜ n
· 使用定理 `TensorProduct.tmul_smul`：tmul_smul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (x : M) (y : N) : x otimesₜ (r • y) = r • x otimesₜ[R] y
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
· 使用定理 `LinearMap.map_smul_of_tower`：map_smul_of_tower [CompatibleSMul M M₂ R S]
 (fₗ : M ->ₗ[S] M₂) (c : R) (x : M) : fₗ (c • x) = c • fₗ x
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …

--- 原说明 ---
Taking the `MultilinearMap.alternatization` of the `MultilinearMap.domCoprod` of
 two
`AlternatingMap`s gives a scaled version of the `AlternatingMap.coprod` of those
 maps.
-/
theorem MultilinearMap.domCoprod_alternization_eq [DecidableEq ιa] [DecidableEq ιb]
    (a : Mᵢ [⋀^ιa]→ₗ[R'] N₁) (b : Mᵢ [⋀^ιb]→ₗ[R'] N₂) :
    MultilinearMap.alternatization
      (MultilinearMap.domCoprod a b : MultilinearMap R' (fun _ : ιa ⊕ ιb => Mᵢ) (N₁ ⊗ N₂)) =
      ((Fintype.card ιa).factorial * (Fintype.card ιb).factorial) • a.domCoprod b := by
  rw [MultilinearMap.domCoprod_alternization, coe_alternatization, coe_alternatization, mul_smul,
    ← AlternatingMap.domCoprod'_apply, ← AlternatingMap.domCoprod'_apply,
    ← TensorProduct.smul_tmul', TensorProduct.tmul_smul,
    LinearMap.map_smul_of_tower AlternatingMap.domCoprod',
    LinearMap.map_smul_of_tower AlternatingMap.domCoprod']
