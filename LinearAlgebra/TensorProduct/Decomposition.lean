/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Scott Carnahan
-/
module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct

/-! # Decomposition of tensor product

In this file, we describe the properties of decomposition under tensor product. Suppose `ℳ` is a
decomposition of an `R`-module `M` indexed by a type `ι`. Given an `R`-module `N`, the `R`-module
`M ⊗[R] N` has a decomposition into pieces `fun i ↦ (ℳ i) ⊗[R] N`. Given a commutative `R`-algebra
`S`, the `S`-module `S ⊗[R] M` has a decomposition `fun i ↦ (ℳ i).baseChange S`.

-/

public section

open TensorProduct LinearMap

namespace DirectSum

variable {ι R M S : Type*}
  [CommSemiring R] [AddCommMonoid M] [Module R M]
  (ℳ : ι → Submodule R M)

section BaseChange

variable [DecidableEq ι] [Decomposition ℳ] [CommSemiring S] [Algebra R S]

/-
**DirectSum.Decomposition.baseChange** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum.Decomp
osition`。
形式化陈述：{ι : Type u_1} →   {R : Type u_2} →     {M : Type u_3} →       {S : Type u
_4} →         [inst : CommSemiring R] →           [inst_1 : AddCommMonoid M] →  
           [inst_2 : _root_.Module R M] →               (ℳ : ι → Submodule R M) 
→                 [inst_3 : DecidableEq ι] →                   [DirectSum.Decomp
osition ℳ] →                     [inst_5 : CommSemiring S] →                    
   [inst_6 : Algebra R S] → DirectSum.Decomposition fun i => Submodule.baseChang
e S (ℳ i)
参数：ℳ : ι → Submodule R M；ℳ i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Decomposition.baseChange : Decomposition fun i ↦ (ℳ i).baseChange S := by
  refine .ofLinearMap _ (lmap (ℳ · |>.toBaseChange S) ∘ₗ
    (directSumRight R S S fun i ↦ ℳ i).toLinearMap ∘ₗ
    ((decomposeLinearEquiv ℳ).baseChange R S)) ?_ ?_
  · simp_rw [← comp_assoc]
    rw [← LinearEquiv.eq_comp_toLinearMap_symm]
    ext
    simp
  · ext : 1
    rw [← LinearMap.cancel_right ((ℳ _).toBaseChange_surjective S)]
    ext : 3
    simp
/-
**DirectSum.toBaseChange_injective** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：toBaseChange_injective (i : ι) : Function.Injective ((ℳ i).toBaseChange S)
参数：i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.Bijective.of_comp_iff`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sor
t u_3} (f : α → β) {g : γ → α},   Function.Bijective g → (Function.Bijective (f 
∘ g) ↔ Function.Bije…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.coe_trans`：coe_trans : (e₁₂.trans e₂₃ : M₁ ->ₛₗ[σ₁₃] M₃) = (
e₂₃ : M₂ ->ₛₗ[σ₂₃] M₃).comp (e₁₂ : M₁ ->ₛₗ[σ₁₂] M₂)
· 使用定理 `LinearEquiv.bijective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
· 使用定理 `DirectSum.of_injective`：of_injective (i : ι) : Function.Injective (of β 
i)
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `DirectSum.lmap_of`：∀ {R : Type u} [inst : Semiring R] {ι : Type v} {M : 
ι → Type w} [inst_1 : (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i : ι) → _root
_.Modul…
-/
theorem toBaseChange_injective (i : ι) : Function.Injective ((ℳ i).toBaseChange S) := fun x y h ↦ by
  have := (Function.Bijective.of_comp_iff (lmap (ℳ · |>.toBaseChange S))
    (by rw [← LinearEquiv.coe_trans]; exact LinearEquiv.bijective _)).1
    (decompose (M := S ⊗[R] M) fun i ↦ (ℳ i).baseChange S).bijective
  refine of_injective (β := fun i ↦ S ⊗[R] ℳ i) i <| this.injective ?_
  simpa using congr(of (fun i ↦ (ℳ i).baseChange S) i $h)
/-
**DirectSum.toBaseChange_bijective** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：toBaseChange_bijective (i : ι) : Function.Bijective ((ℳ i).toBaseChange S)
参数：i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `DirectSum.toBaseChange_injective`：toBaseChange_injective (i : ι) : Funct
ion.Injective ((ℳ i).toBaseChange S)
· 使用引理 `Submodule.toBaseChange_surjective`：toBaseChange_surjective : Function.Su
rjective (p.toBaseChange A)
-/
theorem toBaseChange_bijective (i : ι) : Function.Bijective ((ℳ i).toBaseChange S) :=
  ⟨toBaseChange_injective ℳ i, (ℳ i).toBaseChange_surjective S⟩

end BaseChange

section TensorModule

variable (N : Type*) [AddCommMonoid N] [Module R N]

/-- The submodule of a tensor product corresponding to a decomposition on the left. -/
/-
**DirectSum.decomposeTensor** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：decomposeTensor (i : ι) : Submodule R (M otimes[R] N)
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The submodule of a tensor product corresponding to a decomposition on the left.
-/
def decomposeTensor (i : ι) : Submodule R (M ⊗[R] N) :=
  ((ℳ i).subtype.rTensor N).range
/-
**DirectSum.decomposeTensor_apply** 是 Mathlib 中的一个引理，位于命名空间 `DirectSum`。
形式化陈述：decomposeTensor_apply {i : ι} : decomposeTensor ℳ N i = ((ℳ i).subtype.rTe
nsor N).range
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.toSubMulAction_inj`：toSubMulAction_inj : p.toSubMulAction = q.
toSubMulAction ↔ p = q
-/
lemma decomposeTensor_apply {i : ι} :
    decomposeTensor ℳ N i = ((ℳ i).subtype.rTensor N).range :=
  Submodule.toSubMulAction_inj.mp rfl

variable [DecidableEq ι] [Decomposition ℳ]
/-
**DirectSum.subtype_rTensor_injective** 是 Mathlib 中的一个引理，位于命名空间 `DirectSum`。
形式化陈述：subtype_rTensor_injective (i : ι) : Function.Injective ((ℳ i).subtype.rTen
sor N)
参数：i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.injective_of_comp_eq_id`：injective_of_comp_eq_id : Injective f
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `DirectSum.decomposeLinearEquiv_apply_coe`：∀ {ι : Type u_1} {R : Type u_2
} {M : Type u_3} [inst : DecidableEq ι] [inst_1 : Semiring R] [inst_2 : AddCommM
onoid M]   [inst_3 : _root_.Mo…
· 使用定理 `DirectSum.component.lof_self`：∀ (R : Type u) [inst : Semiring R] {ι : Ty
pe v} {M : ι → Type w} [inst_1 : (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i :
 ι) → _root_.Modul…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma subtype_rTensor_injective (i : ι) :
    Function.Injective ((ℳ i).subtype.rTensor N) :=
  injective_of_comp_eq_id ((ℳ i).subtype.rTensor N)
    ((component R ι (fun i ↦ ℳ i) i ∘ₗ DirectSum.decomposeLinearEquiv ℳ).rTensor N)
    (by ext; simp)

/-- The linear isomorphism to the submodule from the tensor product with a summand. -/
/-
**DirectSum.decomposeTensorEquiv** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：decomposeTensorEquiv (i : ι) : (ℳ i) otimes[R] N ≃ₗ[R] decomposeTensor ℳ N
 i
参数：i : ι。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `DirectSum.subtype_rTensor_injective`：subtype_rTensor_injective (i : ι) :
 Function.Injective ((ℳ i).subtype.rTensor N)

--- 原说明 ---
The linear isomorphism to the submodule from the tensor product with a summand.
-/
noncomputable def decomposeTensorEquiv (i : ι) :
    (ℳ i) ⊗[R] N ≃ₗ[R] decomposeTensor ℳ N i :=
  LinearEquiv.ofInjective ((ℳ i).subtype.rTensor N) (subtype_rTensor_injective ℳ N i)
/-
**DirectSum.decomposeTensorEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 `DirectSum`。
形式化陈述：decomposeTensorEquiv_apply {i : ι} (x : (ℳ i) otimes[R] N) : decomposeTens
orEquiv ℳ N i x = ⟨(ℳ i).subtype.rTensor N x, by convert (decomposeTensorEquiv ℳ
 N i x).property; rfl⟩
参数：x : (ℳ i) otimes[R] N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma decomposeTensorEquiv_apply {i : ι} (x : (ℳ i) ⊗[R] N) :
    decomposeTensorEquiv ℳ N i x =
      ⟨(ℳ i).subtype.rTensor N x, by convert (decomposeTensorEquiv ℳ N i x).property; rfl⟩ := by
  rfl

@[simp]
/-
**DirectSum.val_decomposeTensorEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 `DirectSum`
。
形式化陈述：val_decomposeTensorEquiv_apply {i : ι} (x : (ℳ i) otimes[R] N) : decompose
TensorEquiv ℳ N i x = (ℳ i).subtype.rTensor N x
参数：x : (ℳ i) otimes[R] N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma val_decomposeTensorEquiv_apply {i : ι} (x : (ℳ i) ⊗[R] N) :
    decomposeTensorEquiv ℳ N i x = (ℳ i).subtype.rTensor N x := by rfl
/-
**DirectSum.decomposeTensorEquiv_of_apply** 是 Mathlib 中的一个引理，位于命名空间 `DirectSum`。
形式化陈述：decomposeTensorEquiv_of_apply {i : ι} (x : (ℳ i) otimes[R] N) : congrLinea
rEquiv (fun i => decomposeTensorEquiv ℳ N i) (of (fun i => ↥(ℳ i) otimes[R] N) i
 x) = of (fun i => decomposeTensor ℳ N i) i (decomposeTensorEquiv ℳ N i x)
参数：x : (ℳ i) otimes[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.ext`：∀ {ι : Type v} {β : ι → Type w} [inst : (i : ι) → AddComm
Monoid (β i)] {x y : DirectSum ι β},   (∀ (i : ι), x i = y i) → x = y
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `DirectSum.lmap_of`：∀ {R : Type u} [inst : Semiring R] {ι : Type v} {M : 
ι → Type w} [inst_1 : (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i : ι) → _root
_.Modul…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma decomposeTensorEquiv_of_apply {i : ι} (x : (ℳ i) ⊗[R] N) :
    congrLinearEquiv (fun i ↦ decomposeTensorEquiv ℳ N i) (of (fun i ↦ ↥(ℳ i) ⊗[R] N) i x) =
      of (fun i ↦ decomposeTensor ℳ N i) i (decomposeTensorEquiv ℳ N i x) := by
  ext; simp [coe_congrLinearEquiv]
/-
**DirectSum.decomposeLinearEquiv_comp_subtype** 是 Mathlib 中的一个引理，位于命名空间 `DirectS
um`。
形式化陈述：decomposeLinearEquiv_comp_subtype {i : ι} : decomposeLinearEquiv ℳ ∘ₗ (ℳ i
).subtype = lof R ι (fun i => ℳ i) i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `DirectSum.ext`：∀ {ι : Type v} {β : ι → Type w} [inst : (i : ι) → AddComm
Monoid (β i)] {x y : DirectSum ι β},   (∀ (i : ι), x i = y i) → x = y
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `DirectSum.decomposeLinearEquiv_apply_coe`：∀ {ι : Type u_1} {R : Type u_2
} {M : Type u_3} [inst : DecidableEq ι] [inst_1 : Semiring R] [inst_2 : AddCommM
onoid M]   [inst_3 : _root_.Mo…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma decomposeLinearEquiv_comp_subtype {i : ι} :
    decomposeLinearEquiv ℳ ∘ₗ (ℳ i).subtype = lof R ι (fun i ↦ ℳ i) i := by
  ext; simp
/-
**DirectSum.coe_decomposeTensor_apply** 是 Mathlib 中的一个引理，位于命名空间 `DirectSum`。
形式化陈述：coe_decomposeTensor_apply (x : (⨁ i, decomposeTensor ℳ N i)) : DirectSum.c
oeAddMonoidHom (decomposeTensor ℳ N) x = (DirectSum.decomposeLinearEquiv ℳ).symm
.rTensor N ((TensorProduct.directSumLeft R R (fun i => ℳ i) N).symm <| (DirectSu
m.congrLinearEquiv <| decomposeTensorEquiv ℳ N).symm x)
参数：x : (⨁ i, decomposeTensor ℳ N i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `DirectSum.instSMulCommClass`：∀ {R : Type u} [inst : Semiring R] {ι : Typ
e v} {M : ι → Type w} [inst_1 : (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i : 
ι) → _root_.Modul…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.symm_rTensor`：∀ {R : Type u_1} [inst : CommSemiring R] (M : 
Type u_7) {N : Type u_8} {P : Type u_9} [inst_1 : AddCommMonoid M]   [inst_2 : A
ddCommMonoid N…
· 使用定理 `LinearEquiv.eq_symm_apply`：eq_symm_apply {x y} : y = e.symm x ↔ e y = x
· 使用定理 `DirectSum.induction_on`：∀ {ι : Type v} {β : ι → Type w} [inst : (i : ι) 
→ AddCommMonoid (β i)] [inst_1 : DecidableEq ι]   {motive : (DirectSum ι fun i =
> β i) → Pro…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `TensorProduct.directSumLeft_symm_of`：directSumLeft_symm_of {i : ι₁} (x :
 (M₁ i) otimes[R] M₂') : (directSumLeft R S M₁ M₂').symm ((of (fun i => M₁ i oti
mes[R] M₂') i) x) = rTens…
· 使用定理 `DirectSum.coeAddMonoidHom_of`：coeAddMonoidHom_of {M S : Type*} [Decidabl
eEq ι] [AddCommMonoid M] [SetLike S M] [AddSubmonoidClass S M] (A : ι -> S) (i :
 ι) (x : A i) : Di…
· 使用定理 `LinearEquiv.coe_coe`：coe_coe : ⇑(e : M ->ₛₗ[σ] M₂) = e
· 使用定理 `LinearEquiv.coe_rTensor`：∀ {R : Type u_1} [inst : CommSemiring R] (M : T
ype u_7) {N : Type u_8} {P : Type u_9} [inst_1 : AddCommMonoid M]   [inst_2 : Ad
dCommMonoid N…
· 使用定理 `LinearMap.rTensor_comp_apply`：rTensor_comp_apply (x : N otimes[R] M) : (
g.comp f).rTensor M x = (g.rTensor M) ((f.rTensor M) x)
· 使用引理 `DirectSum.decomposeLinearEquiv_comp_subtype`：decomposeLinearEquiv_comp_s
ubtype {i : ι} : decomposeLinearEquiv ℳ ∘ₗ (ℳ i).subtype = lof R ι (fun i => ℳ i
) i
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用引理 `DirectSum.decomposeTensorEquiv_of_apply`：decomposeTensorEquiv_of_apply {
i : ι} (x : (ℳ i) otimes[R] N) : congrLinearEquiv (fun i => decomposeTensorEquiv
 ℳ N i) (of (fun i => ↥(ℳ i) …
· 使用引理 `DirectSum.decomposeTensorEquiv_apply`：decomposeTensorEquiv_apply {i : ι}
 (x : (ℳ i) otimes[R] N) : decomposeTensorEquiv ℳ N i x = ⟨(ℳ i).subtype.rTensor
 N x, by convert (decompos…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
-/
lemma coe_decomposeTensor_apply (x : (⨁ i, decomposeTensor ℳ N i)) :
    DirectSum.coeAddMonoidHom (decomposeTensor ℳ N) x =
    (DirectSum.decomposeLinearEquiv ℳ).symm.rTensor N
    ((TensorProduct.directSumLeft R R (fun i ↦ ℳ i) N).symm <|
      (DirectSum.congrLinearEquiv <| decomposeTensorEquiv ℳ N).symm x) := by
  rw [← LinearEquiv.symm_rTensor, LinearEquiv.eq_symm_apply]
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    obtain ⟨-, y, rfl⟩ := x
    have : (rTensor N (lof R ι (fun i ↦ ℳ i) i)) y =
        (directSumLeft R R (fun i ↦ ℳ i) N).symm ((of (fun i ↦ ℳ i ⊗[R] N) i) y) :=
      (TensorProduct.directSumLeft_symm_of R R (M₁ := fun i ↦ ℳ i) y).symm
    rw [coeAddMonoidHom_of, LinearEquiv.eq_symm_apply, LinearEquiv.eq_symm_apply,
      ← (LinearEquiv.rTensor N _).coe_coe, LinearEquiv.coe_rTensor, ← rTensor_comp_apply,
      decomposeLinearEquiv_comp_subtype, this, LinearEquiv.apply_symm_apply,
      decomposeTensorEquiv_of_apply, decomposeTensorEquiv_apply]
  | add x y hx hy => simp [hx, hy]

/-- The decomposition of a tensor product induced by a decomposition of the left module. -/
@[reducible]
/-
**DirectSum.tensorDecomposition** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：tensorDecomposition (N : Type*) [AddCommGroup N] [Module R N] : DirectSum.
Decomposition (decomposeTensor ℳ N) where decompose' x
参数：N : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The decomposition of a tensor product induced by a decomposition of the left mod
ule.
-/
noncomputable def tensorDecomposition (N : Type*) [AddCommGroup N] [Module R N] :
    DirectSum.Decomposition (decomposeTensor ℳ N) where
  decompose' x := (DirectSum.congrLinearEquiv <| decomposeTensorEquiv ℳ N)
    (directSumLeft R R (fun i ↦ ℳ i) N <| (DirectSum.decomposeLinearEquiv ℳ).rTensor N x)
  left_inv x := by simp [coe_decomposeTensor_apply ℳ N _, ← LinearEquiv.symm_rTensor]
  right_inv x := by simp [coe_decomposeTensor_apply ℳ N _, ← LinearEquiv.symm_rTensor]

end TensorModule

namespace IsInternal

variable [DecidableEq ι] [CommSemiring S] [Algebra R S]

/-
**DirectSum.IsInternal.baseChange** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum.IsInterna
l`。
形式化陈述：baseChange (hm : IsInternal ℳ) : IsInternal fun i => (ℳ i).baseChange S
参数：hm : IsInternal ℳ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.Decomposition.isInternal`：∀ {ι : Type u_1} {M : Type u_3} {σ :
 Type u_4} [inst : DecidableEq ι] [inst_1 : AddCommMonoid M] [inst_2 : SetLike σ
 M]   [inst_3 : AddSubmo…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem baseChange (hm : IsInternal ℳ) : IsInternal fun i ↦ (ℳ i).baseChange S :=
  haveI := hm.chooseDecomposition
  Decomposition.isInternal _
/-
**DirectSum.IsInternal.toBaseChange_bijective** 是 Mathlib 中的一个定理，位于命名空间 `DirectS
um.IsInternal`。
形式化陈述：toBaseChange_bijective (hm : IsInternal ℳ) (i : ι) : Function.Bijective ((
ℳ i).toBaseChange S)
参数：hm : IsInternal ℳ；i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.toBaseChange_bijective`：toBaseChange_bijective (i : ι) : Funct
ion.Bijective ((ℳ i).toBaseChange S)
-/
theorem toBaseChange_bijective (hm : IsInternal ℳ) (i : ι) :
    Function.Bijective ((ℳ i).toBaseChange S) :=
  haveI := hm.chooseDecomposition
  DirectSum.toBaseChange_bijective ℳ i
/-
**DirectSum.IsInternal.toBaseChange_injective** 是 Mathlib 中的一个定理，位于命名空间 `DirectS
um.IsInternal`。
形式化陈述：toBaseChange_injective (hm : IsInternal ℳ) (i : ι) : Function.Injective ((
ℳ i).toBaseChange S)
参数：hm : IsInternal ℳ；i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `DirectSum.IsInternal.toBaseChange_bijective`：toBaseChange_bijective (hm 
: IsInternal ℳ) (i : ι) : Function.Bijective ((ℳ i).toBaseChange S)
-/
theorem toBaseChange_injective (hm : IsInternal ℳ) (i : ι) :
    Function.Injective ((ℳ i).toBaseChange S) :=
  (toBaseChange_bijective ℳ hm i).injective

end IsInternal

end DirectSum

