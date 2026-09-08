/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
module

public import Mathlib.LinearAlgebra.Contraction

/-!
# The coevaluation map on finite-dimensional vector spaces

Given a finite-dimensional vector space `V` over a field `K` this describes the canonical linear map
from `K` to `V ⊗ Dual K V` which corresponds to the identity function on `V`.

## Tags

coevaluation, dual module, tensor product

## Future work

* Prove that this is independent of the choice of basis on `V`.
-/

@[expose] public section


noncomputable section

section coevaluation

open TensorProduct Module

open TensorProduct

universe u v

variable (K : Type u) [Field K]
variable (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The coevaluation map is a linear map from a field `K` to a finite-dimensional
  vector space `V`. -/
/-
**coevaluation** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：coevaluation : K ->ₗ[K] V otimes[K] Module.Dual K V
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coevaluation map is a linear map from a field `K` to a finite-dimensional
  vector space `V`.
-/
def coevaluation : K →ₗ[K] V ⊗[K] Module.Dual K V :=
  let bV := Basis.ofVectorSpace K V
  (Basis.singleton Unit K).constr K fun _ =>
    ∑ i : Basis.ofVectorSpaceIndex K V, bV i ⊗ₜ[K] bV.coord i
/-
**coevaluation_apply_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coevaluation_apply_one : (coevaluation K V) (1 : K) = let bV
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.constr_apply_fintype`：constr_apply_fintype [Fintype ι] (b :
 Basis ι R M) (f : ι -> M') (x : M) : (constr (M'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Module.Basis.singleton_repr`：singleton_repr (ι R : Type*) [Unique ι] [Se
miring R] (x i) : (Basis.singleton ι R).repr x i = x
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Module.Basis.coe_ofVectorSpace`：coe_ofVectorSpace : ⇑(ofVectorSpace K V)
 = ((↑) : _ -> _)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coevaluation_apply_one :
    (coevaluation K V) (1 : K) =
      let bV := Basis.ofVectorSpace K V
      ∑ i : Basis.ofVectorSpaceIndex K V, bV i ⊗ₜ[K] bV.coord i := by
  simp only [coevaluation]
  rw [(Basis.singleton Unit K).constr_apply_fintype K]
  simp only [Fintype.univ_punit, Finset.sum_const, one_smul, Basis.singleton_repr,
    Basis.equivFun_apply, Basis.coe_ofVectorSpace, Finset.card_singleton]

open TensorProduct

/-- This lemma corresponds to one of the coherence laws for duals in rigid categories, see
  `CategoryTheory.Monoidal.Rigid`. -/
/-
**contractLeft_assoc_coevaluation** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contractLeft_assoc_coevaluation : (contractLeft K V).rTensor _ ∘ₗ (TensorP
roduct.assoc K _ _ _).symm.toLinearMap ∘ₗ (coevaluation K V).lTensor (Module.Dua
l K V) = (TensorProduct.lid K _).symm.toLinearMap ∘ₗ (TensorProduct.rid K _).toL
inearMap
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.ext`：ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).c
ompr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) : g = h
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.compr₂ₛₗ_apply`：compr₂ₛₗ_apply (f : M ->ₛₗ[σ₁₃] N ->ₛₗ[σ₂₃] P)
 (g : P ->ₛₗ[σ₃₄] Q) (m : M) (n : N) : f.compr₂ₛₗ g m n = g (f m n)
· 使用定理 `TensorProduct.mk_apply`：mk_apply (m : M) (n : N) : mk R M N m n = m otim
esₜ n
· 使用定理 `TensorProduct.rid_tmul`：rid_tmul (m : M) (r : R) : (TensorProduct.rid R 
M) (m otimesₜ r) = r • m
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `TensorProduct.lid_symm_apply`：lid_symm_apply (m : M) : (TensorProduct.li
d R M).symm m = 1 otimesₜ m
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `coevaluation_apply_one`：coevaluation_apply_one : (coevaluation K V) (1 :
 K) = let bV
· 使用定理 `TensorProduct.tmul_sum`：tmul_sum (m : M) {α : Type*} (s : Finset α) (n :
 α -> N) : (m otimesₜ[R] ∑ a in s, n a) = ∑ a in s, m otimesₜ[R] n a
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Module.Basis.coe_dualBasis`：coe_dualBasis : ⇑b.dualBasis = b.coord
· 使用定理 `Module.Basis.coord_apply`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_
12} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] (b : Module.…
· 使用定理 `Module.Basis.repr_self_apply`：repr_self_apply (j) [Decidable (i = j)] : 
b.repr (b i) j = if i = j then 1 else 0
· 使用定理 `TensorProduct.ite_tmul`：ite_tmul (x₁ : M) (x₂ : N) (P : Prop) [Decidable
 P] : (if P then x₁ else 0) otimesₜ[R] x₂ = if P then x₁ otimesₜ x₂ else 0
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
This lemma corresponds to one of the coherence laws for duals in rigid categorie
s, see
  `CategoryTheory.Monoidal.Rigid`.
-/
theorem contractLeft_assoc_coevaluation :
    (contractLeft K V).rTensor _ ∘ₗ
        (TensorProduct.assoc K _ _ _).symm.toLinearMap ∘ₗ
          (coevaluation K V).lTensor (Module.Dual K V) =
      (TensorProduct.lid K _).symm.toLinearMap ∘ₗ (TensorProduct.rid K _).toLinearMap := by
  let := Classical.decEq (Basis.ofVectorSpaceIndex K V)
  apply TensorProduct.ext
  apply (Basis.ofVectorSpace K V).dualBasis.ext; intro j; apply LinearMap.ext_ring
  rw [LinearMap.compr₂ₛₗ_apply, LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_toLinearMap]
  rw [rid_tmul, one_smul, lid_symm_apply]
  simp only [LinearMap.lTensor_tmul, coevaluation_apply_one]
  rw [TensorProduct.tmul_sum, map_sum]; simp only [assoc_symm_tmul]
  rw [map_sum]; simp only [LinearMap.rTensor_tmul, contractLeft_apply]
  simp only [Basis.coe_dualBasis, Basis.coord_apply, Basis.repr_self_apply, TensorProduct.ite_tmul]
  rw [Finset.sum_ite_eq']; simp only [Finset.mem_univ, if_true]

/-- This lemma corresponds to one of the coherence laws for duals in rigid categories, see
  `CategoryTheory.Monoidal.Rigid`. -/
/-
**contractLeft_assoc_coevaluation'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contractLeft_assoc_coevaluation' : (contractLeft K V).lTensor _ ∘ₗ (Tensor
Product.assoc K _ _ _).toLinearMap ∘ₗ (coevaluation K V).rTensor V = (TensorProd
uct.rid K _).symm.toLinearMap ∘ₗ (TensorProduct.lid K _).toLinearMap
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.ext`：ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).c
ompr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) : g = h
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.compr₂ₛₗ_apply`：compr₂ₛₗ_apply (f : M ->ₛₗ[σ₁₃] N ->ₛₗ[σ₂₃] P)
 (g : P ->ₛₗ[σ₃₄] Q) (m : M) (n : N) : f.compr₂ₛₗ g m n = g (f m n)
· 使用定理 `TensorProduct.mk_apply`：mk_apply (m : M) (n : N) : mk R M N m n = m otim
esₜ n
· 使用定理 `TensorProduct.lid_tmul`：lid_tmul (m : M) (r : R) : (TensorProduct.lid R 
M : R otimes M -> M) (r otimesₜ m) = r • m
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `TensorProduct.rid_symm_apply`：rid_symm_apply (m : M) : (TensorProduct.ri
d R M).symm m = m otimesₜ 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `coevaluation_apply_one`：coevaluation_apply_one : (coevaluation K V) (1 :
 K) = let bV
· 使用定理 `TensorProduct.sum_tmul`：sum_tmul {α : Type*} (s : Finset α) (m : α -> M)
 (n : N) : (∑ a in s, m a) otimesₜ[R] n = ∑ a in s, m a otimesₜ[R] n
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
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
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Module.Basis.coord_apply`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_
12} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] (b : Module.…
· 使用定理 `Module.Basis.repr_self_apply`：repr_self_apply (j) [Decidable (i = j)] : 
b.repr (b i) j = if i = j then 1 else 0
· 使用定理 `TensorProduct.tmul_ite`：tmul_ite (x₁ : M) (x₂ : N) (P : Prop) [Decidable
 P] : (x₁ otimesₜ[R] if P then x₂ else 0) = if P then x₁ otimesₜ x₂ else 0
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
This lemma corresponds to one of the coherence laws for duals in rigid categorie
s, see
  `CategoryTheory.Monoidal.Rigid`.
-/
theorem contractLeft_assoc_coevaluation' :
    (contractLeft K V).lTensor _ ∘ₗ
        (TensorProduct.assoc K _ _ _).toLinearMap ∘ₗ (coevaluation K V).rTensor V =
      (TensorProduct.rid K _).symm.toLinearMap ∘ₗ (TensorProduct.lid K _).toLinearMap := by
  let := Classical.decEq (Basis.ofVectorSpaceIndex K V)
  apply TensorProduct.ext
  apply LinearMap.ext_ring; apply (Basis.ofVectorSpace K V).ext; intro j
  rw [LinearMap.compr₂ₛₗ_apply, LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_toLinearMap]
  rw [lid_tmul, one_smul, rid_symm_apply]
  simp only [LinearMap.rTensor_tmul, coevaluation_apply_one]
  rw [TensorProduct.sum_tmul, map_sum]; simp only [assoc_tmul]
  rw [map_sum]; simp only [LinearMap.lTensor_tmul, contractLeft_apply]
  simp only [Basis.coord_apply, Basis.repr_self_apply, TensorProduct.tmul_ite]
  rw [Finset.sum_ite_eq]; simp only [Finset.mem_univ, if_true]

end coevaluation

