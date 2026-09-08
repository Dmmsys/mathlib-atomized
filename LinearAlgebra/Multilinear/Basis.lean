/-
Copyright (c) 2021 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Eric Wieser, Daniel Morrison
-/
module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Multilinear.Finsupp

/-!
# Multilinear maps in relation to bases.

This file proves lemmas about the action of multilinear maps on basis vectors and constructs a
basis for multilinear maps given bases on the domain and codomain.

-/

@[expose] public section


open MultilinearMap

variable {ι R : Type*} [CommSemiring R]
  {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  {N : Type*} [AddCommMonoid N] [Module R N]

/-- Two multilinear maps indexed by a `Fintype` are equal if they are equal when all arguments
are basis vectors. -/
/-
**Module.Basis.ext_multilinear** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.Basis.ext_multilinear [Finite ι] {f g : MultilinearMap R M N} {ιM :
 ι -> Type*} (e : forall i, Basis (ιM i) R (M i)) (h : forall v : (i : ι) -> ιM 
i, (f fun i => e i (v i)) = g fun i => e i (v i)) : f = g
参数：e : forall i, Basis (ιM i) R (M i)；h : forall v : (i : ι) -> ιM i, (f fun i =
> e i (v i)) = g fun i => e i (v i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
· 使用定理 `Function.Surjective.piMap`：∀ {ι : Sort u_1} {α : ι → Sort u_2} {β : ι → 
Sort u_3} {f : (i : ι) → α i → β i},   (∀ (i : ι), Function.Surjective (f i)) → 
Function.Surjec…
· 使用定理 `LinearEquiv.surjective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {
M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMono
id M] [inst_…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Module.Basis.repr_symm_apply`：repr_symm_apply (v) : b.repr.symm v = Fins
upp.linearCombination R b v
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MultilinearMap.map_sum_finset`：map_sum_finset [DecidableEq ι] [Fintype ι
] : (f fun i => ∑ j in A i, g i j) = ∑ r in piFinset A, f fun i => g i (r i)
· 使用定理 `MultilinearMap.map_smul_univ`：map_smul_univ [Fintype ι] (c : ι -> R) (m 
: forall i, M₁ i) : (f fun i => c i • m i) = (∏ i, c i) • f m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Two multilinear maps indexed by a `Fintype` are equal if they are equal when all
 arguments
are basis vectors.
-/
theorem Module.Basis.ext_multilinear [Finite ι] {f g : MultilinearMap R M N} {ιM : ι → Type*}
    (e : ∀ i, Basis (ιM i) R (M i))
    (h : ∀ v : (i : ι) → ιM i, (f fun i ↦ e i (v i)) = g fun i ↦ e i (v i)) : f = g := by
  cases nonempty_fintype ι
  classical
  ext m
  rcases Function.Surjective.piMap (fun i ↦ (e i).repr.symm.surjective) m with ⟨x, rfl⟩
  unfold Pi.map
  simp_rw [(e _).repr_symm_apply, Finsupp.linearCombination_apply, Finsupp.sum,
    map_sum_finset, map_smul_univ, h]

namespace Basis

open Module

variable {κ : ι → Type*} (b : (i : ι) → Basis (κ i) R (M i))
  {ι' N : Type*} [AddCommMonoid N] [Module R N] (b' : Basis ι' R N)

open scoped Classical in
/-- A basis for multilinear maps given a finite basis on each domain and a basis on the codomain. -/
/-
**Basis.multilinearMap** 是 Mathlib 中的一个定义，位于命名空间 `Basis`。
形式化陈述：multilinearMap [Finite ι] [forall i, Finite (κ i)] : Basis ((Π i, κ i) × ι
') R (MultilinearMap R M N) where repr
参数：κ i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A basis for multilinear maps given a finite basis on each domain and a basis on 
the codomain.
-/
noncomputable def multilinearMap [Finite ι] [∀ i, Finite (κ i)] :
    Basis ((Π i, κ i) × ι') R (MultilinearMap R M N) where
  repr :=
    have : Fintype ι := Fintype.ofFinite _
    have (i : ι) : Fintype (κ i) := Fintype.ofFinite _
    LinearEquiv.multilinearMapCongrLeft (fun i => (b i).repr.symm) ≪≫ₗ
      (b'.repr).multilinearMapCongrRight R ≪≫ₗ freeFinsuppEquiv.symm

variable [Fintype ι] [∀ i, Finite (κ i)]
/-
**Basis.multilinearMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `Basis`。
形式化陈述：multilinearMap_apply (i : (Π i, κ i) × ι') : Basis.multilinearMap b b' i =
 ((LinearMap.id (M
参数：i : (Π i, κ i) × ι'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearEquiv.trans.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Ty
pe u_4} {M₁ : Type u_8} {M₂ : Type u_9} {M₃ : Type u_10} [inst : Semiring R₁]   
[inst_1 : Semiring…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `LinearEquiv.multilinearMapCongrRight_symm_apply`：∀ {R : Type uR} (S : Ty
pe uS) {ι : Type uι} {M₁ : ι → Type v₁} {M₂ : Type v₂} {M₃ : Type v₃} [inst : Se
miring R]   [inst_1 : (i : ι) → AddCo…
· 使用定理 `Module.Basis.coe_repr_symm`：coe_repr_symm : ↑b.repr.symm = Finsupp.linea
rCombination R b
· 使用定理 `LinearEquiv.multilinearMapCongrLeft_symm_apply`：∀ {R : Type uR} {ι : Typ
e uι} {M₁ : ι → Type v₁} {M₁' : ι → Type v₁'} {M₂ : Type v₂} [inst : CommSemirin
g R]   [inst_1 : (i : ι) → AddCommMo…
· 使用定理 `MultilinearMap.freeFinsuppEquiv_single`：freeFinsuppEquiv_single (p : ((Π
 i, κ i) × ι')) (r : R) (x : Π i, (κ i ->₀ R)) : freeFinsuppEquiv (Finsupp.singl
e p r) x = r • Finsupp.singl…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Module.Basis.coord_apply`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_
12} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] (b : Module.…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem multilinearMap_apply (i : (Π i, κ i) × ι') :
    Basis.multilinearMap b b' i =
      ((LinearMap.id (M := R)).smulRight (b' i.2)).compMultilinearMap
        (MultilinearMap.mkPiRing R ι 1 |>.compLinearMap fun i' => (b i').coord (i.1 i')) := by
  ext x
  simp +instances only [multilinearMap, Basis.coe_ofRepr, LinearEquiv.trans_symm,
    LinearEquiv.symm_symm, LinearEquiv.trans_apply, LinearEquiv.multilinearMapCongrRight_symm_apply,
    Basis.coe_repr_symm, LinearEquiv.multilinearMapCongrLeft_symm_apply, compLinearMap_apply,
    LinearEquiv.coe_coe, LinearMap.compMultilinearMap_apply, freeFinsuppEquiv_single, one_smul,
    Finsupp.linearCombination_single, Basis.coord_apply, mkPiRing_apply, smul_eq_mul, mul_one,
    LinearMap.coe_smulRight, LinearMap.id_coe, id_eq, Subsingleton.elim (Fintype.ofFinite ι)]

/-- The elements of the basis are the maps which scale `b' ii.2` by the
product of all the `ii.1 ·` coordinates along `b i`. -/
/-
**Basis.multilinearMap_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `Basis`。
形式化陈述：multilinearMap_apply_apply (ii : (Π i, κ i) × ι') (v) : Basis.multilinearM
ap b b' ii v = (∏ i, (b i).repr (v i) (ii.1 i)) • b' ii.2
参数：ii : (Π i, κ i) × ι'；v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Basis.multilinearMap_apply`：multilinearMap_apply (i : (Π i, κ i) × ι') :
 Basis.multilinearMap b b' i = ((LinearMap.id (M
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Module.Basis.coord_apply`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_
12} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] (b : Module.…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The elements of the basis are the maps which scale `b' ii.2` by the
product of all the `ii.1 ·` coordinates along `b i`.
-/
theorem multilinearMap_apply_apply (ii : (Π i, κ i) × ι') (v) :
    Basis.multilinearMap b b' ii v = (∏ i, (b i).repr (v i) (ii.1 i)) • b' ii.2 := by
  simp [Basis.multilinearMap_apply]

end Basis

