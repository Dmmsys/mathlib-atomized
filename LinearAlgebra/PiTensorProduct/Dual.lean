/-
Copyright (c) 2025 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Morrison, Sophie Morel
-/
module

public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis

/-!
# Tensor products of dual spaces

## Main definitions

* `PiTensorProduct.dualDistrib`: The canonical linear map from `⨂[R] i, Dual R (M i)` to
  `Dual R (⨂[R] i, M i)`, sending `⨂ₜ[R] i, f i` to the composition of
  `PiTensorProduct.map f` with the linear equivalence `⨂[R] i, R →ₗ R` given by multiplication.

* `PiTensorProduct.dualDistribEquiv`: A linear equivalence between `⨂[R] i, Dual R (M i)`
  and `Dual R (⨂[R] i, M i)` when all `M i` are finite free modules. If
  `f : (i : ι) → Dual R (M i)`, then this equivalence sends `⨂ₜ[R] i, f i` to the composition of
  `PiTensorProduct.map f` with the natural isomorphism `⨂[R] i, R ≃ R` given by multiplication.
-/

@[expose] public section

namespace PiTensorProduct

open PiTensorProduct LinearMap Module TensorProduct

variable {ι : Type*}

section SemiRing

variable {R : Type*} {M : ι → Type*} [CommSemiring R] [Π i, AddCommMonoid (M i)]
  [Π i, Module R (M i)]

/-- The canonical linear map from `⨂[R] i, Dual R (M i)` to `Dual R (⨂[R] i, M i)`,
sending `⨂ₜ[R] i, f i` to the composition of `PiTensorProduct.map f` with
the linear equivalence `⨂[R] i, R →ₗ R` given by multiplication. -/
/-
**PiTensorProduct.dualDistrib** 是 Mathlib 中的一个定义，位于命名空间 `PiTensorProduct`。
形式化陈述：dualDistrib [Finite ι] : (⨂[R] i, Dual R (M i)) ->ₗ[R] Dual R (⨂[R] i, M i
)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical linear map from `⨂[R] i, Dual R (M i)` to `Dual R (⨂[R] i, M i)`,
sending `⨂ₜ[R] i, f i` to the composition of `PiTensorProduct.map f` with
the linear equivalence `⨂[R] i, R →ₗ R` given by multiplication.
-/
noncomputable def dualDistrib [Finite ι] : (⨂[R] i, Dual R (M i)) →ₗ[R] Dual R (⨂[R] i, M i) :=
  haveI := Fintype.ofFinite ι
  (LinearMap.compRight _ (constantBaseRingEquiv ι R).toLinearMap) ∘ₗ piTensorHomMap

@[simp]
/-
**PiTensorProduct.dualDistrib_apply** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：dualDistrib_apply [Fintype ι] (f : Π i, Dual R (M i)) (m : Π i, M i) : dua
lDistrib (⨂ₜ[R] i, f i) (⨂ₜ[R] i, m i) = ∏ i, (f i) (m i)
参数：f : Π i, Dual R (M i)；m : Π i, M i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiTensorProduct.dualDistrib.eq_1`：∀ {ι : Type u_1} {R : Type u_2} {M : ι
 → Type u_3} [inst : CommSemiring R] [inst_1 : (i : ι) → AddCommMonoid (M i)]   
[inst_2 : (i : ι) → _r…
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PiTensorProduct.piTensorHomMap_tprod_tprod`：∀ {ι : Type u_1} {R : Type u
_4} [inst : CommSemiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid
 (s i)]   [inst_2 : (i : ι) → _r…
· 使用定理 `PiTensorProduct.constantBaseRingEquiv_tprod`：constantBaseRingEquiv_tprod
 (x : ι -> R) : constantBaseRingEquiv ι R (tprod R x) = ∏ i, x i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dualDistrib_apply [Fintype ι] (f : Π i, Dual R (M i)) (m : Π i, M i) :
    dualDistrib (⨂ₜ[R] i, f i) (⨂ₜ[R] i, m i) = ∏ i, (f i) (m i) := by
  rw [dualDistrib, Subsingleton.elim (Fintype.ofFinite ι) ‹_›]
  simp

end SemiRing

section Ring

variable {R : Type*} {κ : ι → Type*} {M : ι → Type*} [CommRing R] [Π i, AddCommGroup (M i)]
  [Π i, Module R (M i)]

open scoped Classical in
/-- An inverse to `PiTensorProduct.dualDistrib` given bases. -/
/-
**PiTensorProduct.dualDistribInvOfBasis** 是 Mathlib 中的一个定义，位于命名空间 `PiTensorProdu
ct`。
形式化陈述：dualDistribInvOfBasis [Finite ι] [forall i, Finite (κ i)] (b : Π i, Basis 
(κ i) R (M i)) : Dual R (⨂[R] i, M i) ->ₗ[R] ⨂[R] i, Dual R (M i)
参数：κ i；b : Π i, Basis (κ i) R (M i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An inverse to `PiTensorProduct.dualDistrib` given bases.
-/
noncomputable def dualDistribInvOfBasis [Finite ι] [∀ i, Finite (κ i)]
    (b : Π i, Basis (κ i) R (M i)) :
    Dual R (⨂[R] i, M i) →ₗ[R] ⨂[R] i, Dual R (M i) :=
  haveI := Fintype.ofFinite ι
  haveI := fun i => Fintype.ofFinite (κ i)
  ∑ p : (Π i, κ i), (ringLmapEquivSelf R ℕ _).symm (⨂ₜ[R] i, (b i).dualBasis (p i)) ∘ₗ
    (applyₗ (⨂ₜ[R] i, b i (p i)))

open scoped Classical in
@[simp]
/-
**PiTensorProduct.dualDistribInvOfBasis_apply** 是 Mathlib 中的一个定理，位于命名空间 `PiTenso
rProduct`。
形式化陈述：dualDistribInvOfBasis_apply [Fintype ι] [forall i, Fintype (κ i)] (b : Π i
, Basis (κ i) R (M i)) (f : Dual R (⨂[R] i, M i)) : dualDistribInvOfBasis b f = 
∑ p : (Π i, κ i), f (⨂ₜ[R] i, b i (p i)) • (⨂ₜ[R] i, (b i).dualBasis (p i))
参数：κ i；b : Π i, Basis (κ i) R (M i)；f : Dual R (⨂[R] i, M i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Module.Basis.coe_dualBasis`：coe_dualBasis : ⇑b.dualBasis = b.coord
· 使用定理 `LinearMap.ringLmapEquivSelf_symm_apply`：∀ (R : Type u_1) (S : Type u_4) 
(M : Type u_5) [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : AddCommMonoid
 M]   [inst_3 : _root_.Modul…
· 使用定理 `LinearMap.coe_sum`：coe_sum {ι : Type*} (t : Finset ι) (f : ι -> M ->ₛₗ[σ
₁₂] M₂) : ⇑(∑ i in t, f i) = ∑ i in t, (f i : M -> M₂)
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `LinearMap.applyₗ_apply_apply`：∀ {R : Type u_1} {M : Type u_4} {M₂ : Type
 u_6} [inst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMono
id M₂] [inst_3 : _…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Fintype.instFastSubsingleton`：∀ (α : Type u_4), Meta.FastSubsingleton (F
intype α)
-/
theorem dualDistribInvOfBasis_apply [Fintype ι] [∀ i, Fintype (κ i)] (b : Π i, Basis (κ i) R (M i))
    (f : Dual R (⨂[R] i, M i)) : dualDistribInvOfBasis b f =
    ∑ p : (Π i, κ i), f (⨂ₜ[R] i, b i (p i)) • (⨂ₜ[R] i, (b i).dualBasis (p i)) := by
  simp only [dualDistribInvOfBasis, Basis.coe_dualBasis, ringLmapEquivSelf_symm_apply, coe_sum,
    coe_comp, coe_smulRight, End.one_apply, Finset.sum_apply, Function.comp_apply,
    applyₗ_apply_apply]
  convert! rfl
/-
**PiTensorProduct.dualDistrib_dualDistribInvOfBasis_left_inverse** 是 Mathlib 中的一
个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：dualDistrib_dualDistribInvOfBasis_left_inverse [Finite ι] [forall i, Finit
e (κ i)] (b : Π i, Basis (κ i) R (M i)) : (dualDistrib) ∘ₗ (dualDistribInvOfBasi
s b) = LinearMap.id
参数：κ i；b : Π i, Basis (κ i) R (M i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Module.Basis.coe_dualBasis`：coe_dualBasis : ⇑b.dualBasis = b.coord
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `PiTensorProduct.dualDistribInvOfBasis_apply`：dualDistribInvOfBasis_apply
 [Fintype ι] [forall i, Fintype (κ i)] (b : Π i, Basis (κ i) R (M i)) (f : Dual 
R (⨂[R] i, M i)) : dualDistribInv…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Module.Basis.coord_apply`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_
12} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] (b : Module.…
· 使用定理 `Basis.piTensorProduct_repr_tprod_apply`：Basis.piTensorProduct_repr_tprod
_apply [Fintype ι] (b : Π i, Basis (κ i) R (M i)) (x : Π i, M i) (p : Π i, κ i) 
: (Basis.piTensorProduct b).…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用引理 `Fintype.prod_ite_zero`：prod_ite_zero : (∏ i, if p i then f i else 0) = i
f forall i, p i then ∏ i, f i else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_smul`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a : α) (b c : β),   (if p then b else c) • a = if p the…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Basis.piTensorProduct_apply`：Basis.piTensorProduct_apply [Finite ι] (b :
 Π i, Basis (κ i) R (M i)) (p : Π i, κ i) : Basis.piTensorProduct b p = ⨂ₜ[R] i,
 (b i) (p i)
· 使用定理 `PiTensorProduct.dualDistrib_apply`：dualDistrib_apply [Fintype ι] (f : Π 
i, Dual R (M i)) (m : Π i, M i) : dualDistrib (⨂ₜ[R] i, f i) (⨂ₜ[R] i, m i) = ∏ 
i, (f i) (m i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dualDistrib_dualDistribInvOfBasis_left_inverse [Finite ι] [∀ i, Finite (κ i)]
    (b : Π i, Basis (κ i) R (M i)) :
    (dualDistrib) ∘ₗ (dualDistribInvOfBasis b) = LinearMap.id := by
  have := Fintype.ofFinite ι
  have := fun i => Fintype.ofFinite (κ i)
  classical
  refine (Basis.piTensorProduct b).dualBasis.ext (fun p ↦ ?_)
  refine (Basis.piTensorProduct b).ext (fun q ↦ ?_)
  simp [Finsupp.single_apply, Fintype.prod_ite_zero, ← funext_iff]
/-
**PiTensorProduct.dualDistrib_dualDistribInvOfBasis_right_inverse** 是 Mathlib 中的
一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：dualDistrib_dualDistribInvOfBasis_right_inverse [Finite ι] [forall i, Fini
te (κ i)] (b : Π i, Basis (κ i) R (M i)) : (dualDistribInvOfBasis b) ∘ₗ dualDist
rib = LinearMap.id
参数：κ i；b : Π i, Basis (κ i) R (M i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Module.Basis.ext_elem`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_12}
 [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (
b : Module.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Basis.piTensorProduct_apply`：Basis.piTensorProduct_apply [Finite ι] (b :
 Π i, Basis (κ i) R (M i)) (p : Π i, κ i) : Basis.piTensorProduct b p = ⨂ₜ[R] i,
 (b i) (p i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Module.Basis.coe_dualBasis`：coe_dualBasis : ⇑b.dualBasis = b.coord
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `PiTensorProduct.dualDistribInvOfBasis_apply`：dualDistribInvOfBasis_apply
 [Fintype ι] [forall i, Fintype (κ i)] (b : Π i, Basis (κ i) R (M i)) (f : Dual 
R (⨂[R] i, M i)) : dualDistribInv…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `PiTensorProduct.dualDistrib_apply`：dualDistrib_apply [Fintype ι] (f : Π 
i, Dual R (M i)) (m : Π i, M i) : dualDistrib (⨂ₜ[R] i, f i) (⨂ₜ[R] i, m i) = ∏ 
i, (f i) (m i)
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Module.Basis.coord_apply`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_
12} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] (b : Module.…
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用引理 `Fintype.prod_ite_zero`：prod_ite_zero : (∏ i, if p i then f i else 0) = i
f forall i, p i then ∏ i, f i else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `ite_smul`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a : α) (b c : β),   (if p then b else c) • a = if p the…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Basis.piTensorProduct_repr_tprod_apply`：Basis.piTensorProduct_repr_tprod
_apply [Fintype ι] (b : Π i, Basis (κ i) R (M i)) (x : Π i, M i) (p : Π i, κ i) 
: (Basis.piTensorProduct b).…
（共 32 条，此处仅展示前 30 条）
-/
theorem dualDistrib_dualDistribInvOfBasis_right_inverse [Finite ι] [∀ i, Finite (κ i)]
    (b : Π i, Basis (κ i) R (M i)) :
    (dualDistribInvOfBasis b) ∘ₗ dualDistrib = LinearMap.id := by
  have := Fintype.ofFinite ι
  have := fun i => Fintype.ofFinite (κ i)
  classical
  refine (Basis.piTensorProduct (fun i => (b i).dualBasis)).ext (fun p ↦ ?_)
  refine (Basis.piTensorProduct (fun i => (b i).dualBasis)).ext_elem (fun q ↦ ?_)
  simp [Finsupp.single_apply, Fintype.prod_ite_zero, ← funext_iff]

/-- A linear equivalence between `⨂[R] i, Dual R (M i)` and `Dual R (⨂[R] i, M i)`
given bases for all `M i`. If `f : (i : ι) → Dual R (s i)`, then this equivalence sends
`⨂ₜ[R] i, f i` to the composition of `PiTensorProduct.map f` with the natural
isomorphism `⨂[R] i, R ≃ R` given by multiplication (`constantBaseRingEquiv`). -/
@[simps!]
/-
**PiTensorProduct.dualDistribEquivOfBasis** 是 Mathlib 中的一个定义，位于命名空间 `PiTensorPro
duct`。
形式化陈述：dualDistribEquivOfBasis [Finite ι] [forall i, Finite (κ i)] (b : Π i, Basi
s (κ i) R (M i)) : (⨂[R] i, Dual R (M i)) ≃ₗ[R] Dual R (⨂[R] i, M i)
参数：κ i；b : Π i, Basis (κ i) R (M i)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.dualDistrib_dualDistribInvOfBasis_left_inverse`：dualDist
rib_dualDistribInvOfBasis_left_inverse [Finite ι] [forall i, Finite (κ i)] (b : 
Π i, Basis (κ i) R (M i)) : (dualDistrib) ∘ₗ (dualDi…
· 使用定理 `PiTensorProduct.dualDistrib_dualDistribInvOfBasis_right_inverse`：dualDis
trib_dualDistribInvOfBasis_right_inverse [Finite ι] [forall i, Finite (κ i)] (b 
: Π i, Basis (κ i) R (M i)) : (dualDistribInvOfBasis …

--- 原说明 ---
A linear equivalence between `⨂[R] i, Dual R (M i)` and `Dual R (⨂[R] i, M i)`
given bases for all `M i`. If `f : (i : ι) → Dual R (s i)`, then this equivalenc
e sends
`⨂ₜ[R] i, f i` to the composition of `PiTensorProduct.map f` with the natural
isomorphism `⨂[R] i, R ≃ R` given by multiplication (`constantBaseRingEquiv`).
-/
noncomputable def dualDistribEquivOfBasis [Finite ι] [∀ i, Finite (κ i)]
    (b : Π i, Basis (κ i) R (M i)) : (⨂[R] i, Dual R (M i)) ≃ₗ[R] Dual R (⨂[R] i, M i) :=
  LinearEquiv.ofLinearMap dualDistrib (dualDistribInvOfBasis b)
    (dualDistrib_dualDistribInvOfBasis_left_inverse _)
    (dualDistrib_dualDistribInvOfBasis_right_inverse _)

variable [Π i, Module.Finite R (M i)] [Π i, Module.Free R (M i)]

/-- A linear equivalence between `⨂[R] i, Dual R (M i)` and `Dual R (⨂[R] i, M i)` when all
`M i` are finite free modules. If `f : (i : ι) → Dual R (M i)`, then this equivalence sends
`⨂ₜ[R] i, f i` to the composition of `PiTensorProduct.map f` with the natural
isomorphism `⨂[R] i, R ≃ R` given by multiplication (`constantBaseRingEquiv`). -/
@[simp]
/-
**PiTensorProduct.dualDistribEquiv** 是 Mathlib 中的一个定义，位于命名空间 `PiTensorProduct`。
形式化陈述：dualDistribEquiv [Finite ι] : (⨂[R] i, Dual R (M i)) ≃ₗ[R] Dual R (⨂[R] i,
 M i)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear equivalence between `⨂[R] i, Dual R (M i)` and `Dual R (⨂[R] i, M i)` w
hen all
`M i` are finite free modules. If `f : (i : ι) → Dual R (M i)`, then this equiva
lence sends
`⨂ₜ[R] i, f i` to the composition of `PiTensorProduct.map f` with the natural
isomorphism `⨂[R] i, R ≃ R` given by multiplication (`constantBaseRingEquiv`).
-/
noncomputable def dualDistribEquiv [Finite ι] :
    (⨂[R] i, Dual R (M i)) ≃ₗ[R] Dual R (⨂[R] i, M i) :=
  dualDistribEquivOfBasis (fun i ↦ Module.Free.chooseBasis R (M i))

end Ring

end PiTensorProduct

