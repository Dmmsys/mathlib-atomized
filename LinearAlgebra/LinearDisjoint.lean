/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.LinearAlgebra.TensorProduct.Submodule
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.RingTheory.Flat.Basic

/-!

# Linearly disjoint submodules

This file contains basics about linearly disjoint submodules.

## Mathematical background

We adapt the definitions in <https://en.wikipedia.org/wiki/Linearly_disjoint>.
Let `R` be a commutative ring, `S` be an `R`-algebra (not necessarily commutative).
Let `M` and `N` be `R`-submodules in `S` (`Submodule R S`).

- `M` and `N` are linearly disjoint (`Submodule.LinearDisjoint M N` or simply
  `M.LinearDisjoint N`), if the natural `R`-linear map `M ⊗[R] N →ₗ[R] S`
  (`Submodule.mulMap M N`) induced by the multiplication in `S` is injective.

The following is the first equivalent characterization of linear disjointness:

- `Submodule.LinearDisjoint.linearIndependent_left_of_flat`:
  if `M` and `N` are linearly disjoint, if `N` is a flat `R`-module, then for any family of
  `R`-linearly independent elements `{ m_i }` of `M`, they are also `N`-linearly independent,
  in the sense that the `R`-linear map from `ι →₀ N` to `S` which maps `{ n_i }`
  to the sum of `m_i * n_i` (`Submodule.mulLeftMap N m`) is injective.

- `Submodule.LinearDisjoint.of_basis_left`:
  conversely, if `{ m_i }` is an `R`-basis of `M`, which is also `N`-linearly independent,
  then `M` and `N` are linearly disjoint.

Dually, we have:

- `Submodule.LinearDisjoint.linearIndependent_right_of_flat`:
  if `M` and `N` are linearly disjoint, if `M` is a flat `R`-module, then for any family of
  `R`-linearly independent elements `{ n_i }` of `N`, they are also `M`-linearly independent,
  in the sense that the `R`-linear map from `ι →₀ M` to `S` which maps `{ m_i }`
  to the sum of `m_i * n_i` (`Submodule.mulRightMap M n`) is injective.

- `Submodule.LinearDisjoint.of_basis_right`:
  conversely, if `{ n_i }` is an `R`-basis of `N`, which is also `M`-linearly independent,
  then `M` and `N` are linearly disjoint.

The following is the second equivalent characterization of linear disjointness:

- `Submodule.LinearDisjoint.linearIndependent_mul_of_flat`:
  if `M` and `N` are linearly disjoint, if one of `M` and `N` is flat, then for any family of
  `R`-linearly independent elements `{ m_i }` of `M`, and any family of
  `R`-linearly independent elements `{ n_j }` of `N`, the family `{ m_i * n_j }` in `S` is
  also `R`-linearly independent.

- `Submodule.LinearDisjoint.of_basis_mul`:
  conversely, if `{ m_i }` is an `R`-basis of `M`, if `{ n_i }` is an `R`-basis of `N`,
  such that the family `{ m_i * n_j }` in `S` is `R`-linearly independent,
  then `M` and `N` are linearly disjoint.

## Other main results

- `Submodule.LinearDisjoint.symm_of_commute`, `Submodule.linearDisjoint_comm_of_commute`:
  linear disjointness is symmetric under some commutative conditions.

- `Submodule.LinearDisjoint.map`:
  linear disjointness is preserved by injective algebra homomorphisms.

- `Submodule.linearDisjoint_op`:
  linear disjointness is preserved by taking multiplicative opposite.

- `Submodule.LinearDisjoint.of_le_left_of_flat`, `Submodule.LinearDisjoint.of_le_right_of_flat`,
  `Submodule.LinearDisjoint.of_le_of_flat_left`, `Submodule.LinearDisjoint.of_le_of_flat_right`:
  linear disjointness is preserved by taking submodules under some flatness conditions.

- `Submodule.LinearDisjoint.of_linearDisjoint_fg_left`,
  `Submodule.LinearDisjoint.of_linearDisjoint_fg_right`,
  `Submodule.LinearDisjoint.of_linearDisjoint_fg`:
  conversely, if any finitely generated submodules of `M` and `N` are linearly disjoint,
  then `M` and `N` themselves are linearly disjoint.

- `Submodule.LinearDisjoint.bot_left`, `Submodule.LinearDisjoint.bot_right`:
  the zero module is linearly disjoint with any other submodules.

- `Submodule.LinearDisjoint.one_left`, `Submodule.LinearDisjoint.one_right`:
  the image of `R` in `S` is linearly disjoint with any other submodules.

- `Submodule.LinearDisjoint.of_left_le_one_of_flat`,
  `Submodule.LinearDisjoint.of_right_le_one_of_flat`:
  if a submodule is contained in the image of `R` in `S`, then it is linearly disjoint with
  any other submodules, under some flatness conditions.

- `Submodule.LinearDisjoint.not_linearIndependent_pair_of_commute_of_flat`,
  `Submodule.LinearDisjoint.rank_inf_le_one_of_commute_of_flat`:
  if `M` and `N` are linearly disjoint, if one of `M` and `N` is flat, then any two commutative
  elements contained in the intersection of `M` and `N` are not `R`-linearly independent (namely,
  their span is not `R ^ 2`). In particular, if any two elements in the intersection of `M` and `N`
  are commutative, then the rank of the intersection of `M` and `N` is at most one.

  These results are stated using a bundled version (i.e. `a : ↥(M ⊓ N)`). If you want a non-bundled
  version (i.e. `a : S` with `ha : a ∈ M ⊓ N`), you may use `LinearIndependent.of_comp` and
  `FinVec.map_eq` (in `Mathlib/Data/Fin/Tuple/Reflection.lean`),
  see the following code snippet:

  ```
  have h := H.not_linearIndependent_pair_of_commute_of_flat hf ⟨a, ha⟩ ⟨b, hb⟩ hc
  contrapose! h
  refine .of_comp (M ⊓ N).subtype ?_
  convert h
  exact (FinVec.map_eq _ _).symm
  ```

- `Submodule.LinearDisjoint.rank_le_one_of_commute_of_flat_of_self`:
  if `M` and itself are linearly disjoint, if `M` is flat, if any two elements in `M`
  are commutative, then the rank of `M` is at most one.

The results with name containing "`of_commute`" also have corresponding specialized versions
assuming `S` is commutative.

## Tags

linearly disjoint, linearly independent, tensor product

-/

@[expose] public section

open Module
open scoped TensorProduct

noncomputable section

universe u v w

namespace Submodule

variable {R : Type u} {S : Type v}

section Semiring

variable [CommSemiring R] [Semiring S] [Algebra R S]

variable (M N : Submodule R S)

/-- Two submodules `M` and `N` in an algebra `S` over `R` are linearly disjoint if the natural map
`M ⊗[R] N →ₗ[R] S` induced by multiplication in `S` is injective. -/
@[mk_iff]
/-
**Submodule.LinearDisjoint** 是 Mathlib 中的一个归纳类型，位于命名空间 `Submodule`。
形式化陈述：{R : Type u} →   {S : Type v} →     [inst : CommSemiring R] → [inst_1 : Se
miring S] → [inst_2 : Algebra R S] → Submodule R S → Submodule R S → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two submodules `M` and `N` in an algebra `S` over `R` are linearly disjoint if t
he natural map
`M ⊗[R] N →ₗ[R] S` induced by multiplication in `S` is injective.
-/
protected structure LinearDisjoint : Prop where
  injective : Function.Injective (mulMap M N)

variable {M N}

/-- If `M` and `N` are linearly disjoint submodules, then there is the natural isomorphism
`M ⊗[R] N ≃ₗ[R] M * N` induced by multiplication in `S`. -/
/-
**Submodule.LinearDisjoint.mulMap** 是 Mathlib 中的一个定义，位于命名空间 `Submodule.LinearDis
joint`。
形式化陈述：{R : Type u} →   {S : Type v} →     [inst : CommSemiring R] →       [inst_
1 : Semiring S] →         [inst_2 : Algebra R S] → {M N : Submodule R S} → M.Lin
earDisjoint N → TensorProduct R ↥M ↥N ≃ₗ[R] ↥(M * N)
参数：M * N。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Submodule.LinearDisjoint.injective`：∀ {R : Type u} {S : Type v} [inst : 
CommSemiring R] [inst_1 : Semiring S] [inst_2 : Algebra R S] {M N : Submodule R 
S},   M.LinearDisjoint N…
· 使用定理 `Submodule.mulMap_range`：mulMap_range : LinearMap.range (mulMap M N) = M 
* N

--- 原说明 ---
If `M` and `N` are linearly disjoint submodules, then there is the natural isomo
rphism
`M ⊗[R] N ≃ₗ[R] M * N` induced by multiplication in `S`.
-/
protected def LinearDisjoint.mulMap (H : M.LinearDisjoint N) : M ⊗[R] N ≃ₗ[R] M * N :=
  LinearEquiv.ofInjective (M.mulMap N) H.injective ≪≫ₗ LinearEquiv.ofEq _ _ (mulMap_range M N)

@[simp]
/-
**Submodule.LinearDisjoint.val_mulMap_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.
LinearDisjoint`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommSemiring R] [inst_1 : Semiring S] 
[inst_2 : Algebra R S] {M N : Submodule R S}   (H : M.LinearDisjoint N) (m : ↥M)
 (n : ↥N), ↑(H.mulMap (m ⊗ₜ[R] n)) = ↑m * ↑n
参数：H : M.LinearDisjoint N；m : ↥M；n : ↥N；H.mulMap (m ⊗ₜ[R] n)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem LinearDisjoint.val_mulMap_tmul (H : M.LinearDisjoint N) (m : M) (n : N) :
    (H.mulMap (m ⊗ₜ[R] n) : S) = m.1 * n.1 := rfl

@[nontriviality]
/-
**Submodule.LinearDisjoint.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.
LinearDisjoint`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommSemiring R] [inst_1 : Semiring S] 
[inst_2 : Algebra R S] {M N : Submodule R S}   [Subsingleton R], M.LinearDisjoin
t N
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.injective_of_subsingleton`：∀ {α : Sort u_1} {β : Sort u_2} [Sub
singleton α] (f : α → β), Function.Injective f
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `instSubsingletonSubtype_mathlib`：∀ {α : Sort u_1} [Subsingleton α] (p : 
α → Prop), Subsingleton (Subtype p)
· 使用定理 `Module.subsingleton`：∀ (R : Type u_5) (M : Type u_6) [inst : MonoidWithZ
ero R] [Subsingleton R] [inst_2 : Zero M] [MulActionWithZero R M],   Subsingleto
n M
-/
theorem LinearDisjoint.of_subsingleton [Subsingleton R] : M.LinearDisjoint N :=
  haveI : Subsingleton S := Module.subsingleton R S
  ⟨Function.injective_of_subsingleton _⟩

@[nontriviality]
/-
**Submodule.LinearDisjoint.of_subsingleton_top** 是 Mathlib 中的一个定理，位于命名空间 `Submod
ule.LinearDisjoint`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommSemiring R] [inst_1 : Semiring S] 
[inst_2 : Algebra R S] {M N : Submodule R S}   [Subsingleton S], M.LinearDisjoin
t N
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.injective_of_subsingleton`：∀ {α : Sort u_1} {β : Sort u_2} [Sub
singleton α] (f : α → β), Function.Injective f
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `instSubsingletonSubtype_mathlib`：∀ {α : Sort u_1} [Subsingleton α] (p : 
α → Prop), Subsingleton (Subtype p)
-/
theorem LinearDisjoint.of_subsingleton_top [Subsingleton S] : M.LinearDisjoint N :=
  ⟨Function.injective_of_subsingleton _⟩

set_option backward.isDefEq.respectTransparency false in
/-- Linear disjointness is preserved by taking multiplicative opposite. -/
/-
**Submodule.linearDisjoint_op** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：linearDisjoint_op : M.LinearDisjoint N ↔ (equivOpposite.symm (MulOpposite.
op N)).LinearDisjoint (equivOpposite.symm (MulOpposite.op M))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mulMap_op`：mulMap_op : mulMap (equivOpposite.symm (MulOpposite
.op M)) (equivOpposite.symm (MulOpposite.op N)) = (MulOpposite.opLinearEquiv R).
toLinearM…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Linear disjointness is preserved by taking multiplicative opposite.
-/
theorem linearDisjoint_op :
    M.LinearDisjoint N ↔ (equivOpposite.symm (MulOpposite.op N)).LinearDisjoint
      (equivOpposite.symm (MulOpposite.op M)) := by
  simp only [linearDisjoint_iff, mulMap_op, LinearMap.coe_comp,
    LinearEquiv.coe_coe, EquivLike.comp_injective, EquivLike.injective_comp]

alias ⟨LinearDisjoint.op, LinearDisjoint.of_op⟩ := linearDisjoint_op

/-- Linear disjointness is symmetric if elements in the module commute. -/
/-
**Submodule.LinearDisjoint.symm_of_commute** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.
LinearDisjoint`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommSemiring R] [inst_1 : Semiring S] 
[inst_2 : Algebra R S] {M N : Submodule R S},   M.LinearDisjoint N → (∀ (m : ↥M)
 (n : ↥N), Commute ↑m ↑n) → N.LinearDisjoint M
参数：∀ (m : ↥M) (n : ↥N), Commute ↑m ↑n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.linearDisjoint_iff`：∀ {R : Type u} {S : Type v} [inst : CommSe
miring R] [inst_1 : Semiring S] [inst_2 : Algebra R S] (M N : Submodule R S),   
M.LinearDisjoint N…
· 使用定理 `Submodule.mulMap_comm_of_commute`：mulMap_comm_of_commute (hc : forall (m
 : M) (n : N), Commute m.1 n.1) : mulMap N M = mulMap M N ∘ₗ TensorProduct.comm 
R N M
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Equiv.injective_comp`：injective_comp (e : α ≃ β) (f : β -> γ) : Injectiv
e (f ∘ e) ↔ Injective f
· 使用定理 `Submodule.LinearDisjoint.injective`：∀ {R : Type u} {S : Type v} [inst : 
CommSemiring R] [inst_1 : Semiring S] [inst_2 : Algebra R S] {M N : Submodule R 
S},   M.LinearDisjoint N…

--- 原说明 ---
Linear disjointness is symmetric if elements in the module commute.
-/
theorem LinearDisjoint.symm_of_commute (H : M.LinearDisjoint N)
    (hc : ∀ (m : M) (n : N), Commute m.1 n.1) : N.LinearDisjoint M := by
  rw [linearDisjoint_iff, mulMap_comm_of_commute M N hc]
  exact ((TensorProduct.comm R N M).toEquiv.injective_comp _).2 H.injective

/-- Linear disjointness is symmetric if elements in the module commute. -/
/-
**Submodule.linearDisjoint_comm_of_commute** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`
。
形式化陈述：linearDisjoint_comm_of_commute (hc : forall (m : M) (n : N), Commute m.1 n
.1) : M.LinearDisjoint N ↔ N.LinearDisjoint M
参数：hc : forall (m : M) (n : N), Commute m.1 n.1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.LinearDisjoint.symm_of_commute`：∀ {R : Type u} {S : Type v} [i
nst : CommSemiring R] [inst_1 : Semiring S] [inst_2 : Algebra R S] {M N : Submod
ule R S},   M.LinearDisjoint N…
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a

--- 原说明 ---
Linear disjointness is symmetric if elements in the module commute.
-/
theorem linearDisjoint_comm_of_commute
    (hc : ∀ (m : M) (n : N), Commute m.1 n.1) : M.LinearDisjoint N ↔ N.LinearDisjoint M :=
  ⟨fun H ↦ H.symm_of_commute hc, fun H ↦ H.symm_of_commute fun _ _ ↦ (hc _ _).symm⟩

namespace LinearDisjoint

/-- Linear disjointness is preserved by injective algebra homomorphisms. -/
/-
**Submodule.LinearDisjoint.map** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.LinearDisjoi
nt`。
形式化陈述：map (H : M.LinearDisjoint N) {T : Type w} [Semiring T] [Algebra R T] (f : 
S ->ₐ[R] T) (hf : Function.Injective f) : (M.map (f : S ->ₗ[R] T)).LinearDisjoin
t (N.map (f : S ->ₗ[R] T))
参数：H : M.LinearDisjoint N；f : S ->ₐ[R] T；hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.linearDisjoint_iff`：∀ {R : Type u} {S : Type v} [inst : CommSe
miring R] [inst_1 : Semiring S] [inst_2 : Algebra R S] (M N : Submodule R S),   
M.LinearDisjoint N…
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Function.Injective.of_comp_right`：∀ {α : Sort u_1} {β : Sort u_2} {γ : S
ort u_3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Surjec
tive g → Function.Inje…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.coe_mulMap_comp_eq`：coe_mulMap_comp_eq {T : Type w} [Semiring 
T] [Algebra R T] (f : S ->ₐ[R] T) : mulMap (M.map (f : S ->ₗ[R] T)) (N.map (f : 
S ->ₗ[R] T)) ∘ Ten…
· 使用定理 `TensorProduct.map_surjective`：TensorProduct.map_surjective : Function.Su
rjective (TensorProduct.map g g')
· 使用定理 `LinearMap.submoduleMap_surjective`：submoduleMap_surjective [RingHomSurje
ctive σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R M) : Function.Surjective (f.sub
moduleMap p)

--- 原说明 ---
Linear disjointness is preserved by injective algebra homomorphisms.
-/
theorem map (H : M.LinearDisjoint N) {T : Type w} [Semiring T] [Algebra R T]
    (f : S →ₐ[R] T) (hf : Function.Injective f) :
    (M.map (f : S →ₗ[R] T)).LinearDisjoint (N.map (f : S →ₗ[R] T)) := by
  rw [linearDisjoint_iff] at H ⊢
  have := hf.comp H
  rw [← coe_mulMap_comp_eq] at this
  refine this.of_comp_right ?_
  apply TensorProduct.map_surjective <;> exact LinearMap.submoduleMap_surjective _ _

variable (M N)

/-- If `{ m_i }` is an `R`-basis of `M`, which is also `N`-linearly independent
(in this result it is stated as `Submodule.mulLeftMap` is injective),
then `M` and `N` are linearly disjoint. -/
/-
**Submodule.LinearDisjoint.of_basis_left'** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.L
inearDisjoint`。
形式化陈述：of_basis_left' {ι : Type*} (m : Basis ι R M) (H : Function.Injective (mulL
eftMap N m)) : M.LinearDisjoint N
参数：m : Basis ι R M；H : Function.Injective (mulLeftMap N m)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `Submodule.mulLeftMap_eq_mulMap_comp`：mulLeftMap_eq_mulMap_comp {ι : Type
*} [DecidableEq ι] (m : ι -> M) : mulLeftMap N m = mulMap M N ∘ₗ LinearMap.rTens
or N (Finsupp.linearCombi…

--- 原说明 ---
If `{ m_i }` is an `R`-basis of `M`, which is also `N`-linearly independent
(in this result it is stated as `Submodule.mulLeftMap` is injective),
then `M` and `N` are linearly disjoint.
-/
theorem of_basis_left' {ι : Type*} (m : Basis ι R M)
    (H : Function.Injective (mulLeftMap N m)) : M.LinearDisjoint N := by
  classical simp_rw [mulLeftMap_eq_mulMap_comp, ← Basis.coe_repr_symm,
    ← LinearEquiv.coe_rTensor, LinearEquiv.comp_coe, LinearMap.coe_comp,
    LinearEquiv.coe_coe, EquivLike.injective_comp] at H
  exact ⟨H⟩

/-- If `{ n_i }` is an `R`-basis of `N`, which is also `M`-linearly independent
(in this result it is stated as `Submodule.mulRightMap` is injective),
then `M` and `N` are linearly disjoint. -/
/-
**Submodule.LinearDisjoint.of_basis_right'** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.
LinearDisjoint`。
形式化陈述：of_basis_right' {ι : Type*} (n : Basis ι R N) (H : Function.Injective (mul
RightMap M n)) : M.LinearDisjoint N
参数：n : Basis ι R N；H : Function.Injective (mulRightMap M n)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `Submodule.mulRightMap_eq_mulMap_comp`：mulRightMap_eq_mulMap_comp {ι : Ty
pe*} [DecidableEq ι] (n : ι -> N) : mulRightMap M n = mulMap M N ∘ₗ LinearMap.lT
ensor M (Finsupp.linearCom…

--- 原说明 ---
If `{ n_i }` is an `R`-basis of `N`, which is also `M`-linearly independent
(in this result it is stated as `Submodule.mulRightMap` is injective),
then `M` and `N` are linearly disjoint.
-/
theorem of_basis_right' {ι : Type*} (n : Basis ι R N)
    (H : Function.Injective (mulRightMap M n)) : M.LinearDisjoint N := by
  classical simp_rw [mulRightMap_eq_mulMap_comp, ← Basis.coe_repr_symm,
    ← LinearEquiv.coe_lTensor, LinearEquiv.comp_coe, LinearMap.coe_comp,
    LinearEquiv.coe_coe, EquivLike.injective_comp] at H
  exact ⟨H⟩

/-- If `{ m_i }` is an `R`-basis of `M`, if `{ n_i }` is an `R`-basis of `N`,
such that the family `{ m_i * n_j }` in `S` is `R`-linearly independent
(in this result it is stated as the relevant `Finsupp.linearCombination` is injective),
then `M` and `N` are linearly disjoint. -/
/-
**Submodule.LinearDisjoint.of_basis_mul'** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.Li
nearDisjoint`。
形式化陈述：of_basis_mul' {κ ι : Type*} (m : Basis κ R M) (n : Basis ι R N) (H : Funct
ion.Injective (Finsupp.linearCombination R fun i : κ × ι => (m i.1 * n i.2 : S))
) : M.LinearDisjoint N
参数：m : Basis κ R M；n : Basis ι R N；H : Function.Injective (Finsupp.linearCombina
tion R fun i : κ × ι => (m i.1 * n i.2 : S))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.lhom_ext'`：lhom_ext' ⦃φ ψ : (α ->₀ M) ->ₛₗ[σ₁₂] N⦄ (h : forall a
, φ.comp (lsingle a) = ψ.comp (lsingle a)) : φ = ψ
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finsuppTensorFinsupp'_symm_single_eq_single_one_tmul`：∀ (R : Type u_1) (
ι : Type u_5) (κ : Type u_6) [inst : CommSemiring R] (i : ι × κ) (r : R),   ((fi
nsuppTensorFinsupp' R ι κ).symm fun₀ | i =…
· 使用定理 `Module.Basis.repr_symm_apply`：repr_symm_apply (v) : b.repr.symm v = Fins
upp.linearCombination R b v
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `{ m_i }` is an `R`-basis of `M`, if `{ n_i }` is an `R`-basis of `N`,
such that the family `{ m_i * n_j }` in `S` is `R`-linearly independent
(in this result it is stated as the relevant `Finsupp.linearCombination` is inje
ctive),
then `M` and `N` are linearly disjoint.
-/
theorem of_basis_mul' {κ ι : Type*} (m : Basis κ R M) (n : Basis ι R N)
    (H : Function.Injective (Finsupp.linearCombination R fun i : κ × ι ↦ (m i.1 * n i.2 : S))) :
    M.LinearDisjoint N := by
  let i0 := (finsuppTensorFinsupp' R κ ι).symm
  let i1 := TensorProduct.congr m.repr n.repr
  let i := mulMap M N ∘ₗ (i0.trans i1.symm).toLinearMap
  have : i = Finsupp.linearCombination R fun i : κ × ι ↦ (m i.1 * n i.2 : S) := by
    ext x
    simp [i, i0, i1, finsuppTensorFinsupp'_symm_single_eq_single_one_tmul]
  simp_rw [← this, i, LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.injective_comp] at H
  exact ⟨H⟩

/-- The zero module is linearly disjoint with any other submodules. -/
/-
**Submodule.LinearDisjoint.bot_left** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.LinearD
isjoint`。
形式化陈述：bot_left : (⊥ : Submodule R S).LinearDisjoint N
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.injective_of_subsingleton`：∀ {α : Sort u_1} {β : Sort u_2} [Sub
singleton α] (f : α → β), Function.Injective f
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α

--- 原说明 ---
The zero module is linearly disjoint with any other submodules.
-/
theorem bot_left : (⊥ : Submodule R S).LinearDisjoint N :=
  ⟨Function.injective_of_subsingleton _⟩

/-- The zero module is linearly disjoint with any other submodules. -/
/-
**Submodule.LinearDisjoint.bot_right** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.Linear
Disjoint`。
形式化陈述：bot_right : M.LinearDisjoint (⊥ : Submodule R S)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.injective_of_subsingleton`：∀ {α : Sort u_1} {β : Sort u_2} [Sub
singleton α] (f : α → β), Function.Injective f
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α

--- 原说明 ---
The zero module is linearly disjoint with any other submodules.
-/
theorem bot_right : M.LinearDisjoint (⊥ : Submodule R S) :=
  ⟨Function.injective_of_subsingleton _⟩

/-- The image of `R` in `S` is linearly disjoint with any other submodules. -/
/-
**Submodule.LinearDisjoint.one_left** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.LinearD
isjoint`。
形式化陈述：one_left : (1 : Submodule R S).LinearDisjoint N
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.linearDisjoint_iff`：∀ {R : Type u} {S : Type v} [inst : CommSe
miring R] [inst_1 : Semiring S] [inst_2 : Algebra R S] (M N : Submodule R S),   
M.LinearDisjoint N…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.toSubmodule_bot`：toSubmodule_bot : Subalgebra.toSubmodule (⊥ : S
ubalgebra R A) = 1
· 使用定理 `Submodule.mulMap_one_left_eq`：mulMap_one_left_eq : mulMap (Subalgebra.to
Submodule ⊥) N = N.subtype ∘ₗ N.lTensorOne.toLinearMap
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Submodule.injective_subtype`：injective_subtype : Injective p.subtype
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…

--- 原说明 ---
The image of `R` in `S` is linearly disjoint with any other submodules.
-/
theorem one_left : (1 : Submodule R S).LinearDisjoint N := by
  rw [linearDisjoint_iff, ← Algebra.toSubmodule_bot, mulMap_one_left_eq]
  exact N.injective_subtype.comp N.lTensorOne.injective

/-- The image of `R` in `S` is linearly disjoint with any other submodules. -/
/-
**Submodule.LinearDisjoint.one_right** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.Linear
Disjoint`。
形式化陈述：one_right : M.LinearDisjoint (1 : Submodule R S)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.linearDisjoint_iff`：∀ {R : Type u} {S : Type v} [inst : CommSe
miring R] [inst_1 : Semiring S] [inst_2 : Algebra R S] (M N : Submodule R S),   
M.LinearDisjoint N…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.toSubmodule_bot`：toSubmodule_bot : Subalgebra.toSubmodule (⊥ : S
ubalgebra R A) = 1
· 使用定理 `Submodule.mulMap_one_right_eq`：mulMap_one_right_eq : mulMap M (Subalgebr
a.toSubmodule ⊥) = M.subtype ∘ₗ M.rTensorOne.toLinearMap
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Submodule.injective_subtype`：injective_subtype : Injective p.subtype
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…

--- 原说明 ---
The image of `R` in `S` is linearly disjoint with any other submodules.
-/
theorem one_right : M.LinearDisjoint (1 : Submodule R S) := by
  rw [linearDisjoint_iff, ← Algebra.toSubmodule_bot, mulMap_one_right_eq]
  exact M.injective_subtype.comp M.rTensorOne.injective

/-- If for any finitely generated submodules `M'` of `M`, `M'` and `N` are linearly disjoint,
then `M` and `N` themselves are linearly disjoint. -/
/-
**Submodule.LinearDisjoint.of_linearDisjoint_fg_left** 是 Mathlib 中的一个定理，位于命名空间 `
Submodule.LinearDisjoint`。
形式化陈述：of_linearDisjoint_fg_left (H : forall M' : Submodule R S, M' <= M -> M'.FG
 -> M'.LinearDisjoint N) : M.LinearDisjoint N
参数：H : forall M' : Submodule R S, M' <= M -> M'.FG -> M'.LinearDisjoint N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.linearDisjoint_iff`：∀ {R : Type u} {S : Type v} [inst : CommSe
miring R] [inst_1 : Semiring S] [inst_2 : Algebra R S] (M N : Submodule R S),   
M.LinearDisjoint N…
· 使用定理 `TensorProduct.exists_finite_submodule_left_of_setFinite'`：exists_finite_
submodule_left_of_setFinite' (s : Set (M₁ otimes[R] N₁)) (hs : s.Finite) : exist
s (M' : Submodule R M) (hM : M' <= M₁), Module…
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Submodule.LinearDisjoint.injective`：∀ {R : Type u} {S : Type v} [inst : 
CommSemiring R] [inst_1 : Semiring S] [inst_2 : Algebra R S] {M N : Submodule R 
S},   M.LinearDisjoint N…
· 使用定理 `Module.Finite.iff_fg`：iff_fg {N : Submodule R M} : Module.Finite R N ↔ N
.FG
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.mulMap_comp_rTensor`：mulMap_comp_rTensor {M' : Submodule R S} 
(hM : M' <= M) : mulMap M N ∘ₗ (inclusion hM).rTensor N = mulMap M' N

--- 原说明 ---
If for any finitely generated submodules `M'` of `M`, `M'` and `N` are linearly 
disjoint,
then `M` and `N` themselves are linearly disjoint.
-/
theorem of_linearDisjoint_fg_left
    (H : ∀ M' : Submodule R S, M' ≤ M → M'.FG → M'.LinearDisjoint N) :
    M.LinearDisjoint N := (linearDisjoint_iff _ _).2 fun x y hxy ↦ by
  obtain ⟨M', hM, hFG, h⟩ :=
    TensorProduct.exists_finite_submodule_left_of_setFinite' {x, y} (Set.toFinite _)
  rw [Module.Finite.iff_fg] at hFG
  obtain ⟨x', hx'⟩ := h (show x ∈ {x, y} by simp)
  obtain ⟨y', hy'⟩ := h (show y ∈ {x, y} by simp)
  rw [← hx', ← hy']; congr
  exact (H M' hM hFG).injective (by simp [← mulMap_comp_rTensor _ hM, hx', hy', hxy])

/-- If for any finitely generated submodules `N'` of `N`, `M` and `N'` are linearly disjoint,
then `M` and `N` themselves are linearly disjoint. -/
/-
**Submodule.LinearDisjoint.of_linearDisjoint_fg_right** 是 Mathlib 中的一个定理，位于命名空间 
`Submodule.LinearDisjoint`。
形式化陈述：of_linearDisjoint_fg_right (H : forall N' : Submodule R S, N' <= N -> N'.F
G -> M.LinearDisjoint N') : M.LinearDisjoint N
参数：H : forall N' : Submodule R S, N' <= N -> N'.FG -> M.LinearDisjoint N'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.linearDisjoint_iff`：∀ {R : Type u} {S : Type v} [inst : CommSe
miring R] [inst_1 : Semiring S] [inst_2 : Algebra R S] (M N : Submodule R S),   
M.LinearDisjoint N…
· 使用定理 `TensorProduct.exists_finite_submodule_right_of_setFinite'`：exists_finite
_submodule_right_of_setFinite' (s : Set (M₁ otimes[R] N₁)) (hs : s.Finite) : exi
sts (N' : Submodule R N) (hN : N' <= N₁), Modul…
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Submodule.LinearDisjoint.injective`：∀ {R : Type u} {S : Type v} [inst : 
CommSemiring R] [inst_1 : Semiring S] [inst_2 : Algebra R S] {M N : Submodule R 
S},   M.LinearDisjoint N…
· 使用定理 `Module.Finite.iff_fg`：iff_fg {N : Submodule R M} : Module.Finite R N ↔ N
.FG
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.mulMap_comp_lTensor`：mulMap_comp_lTensor {N' : Submodule R S} 
(hN : N' <= N) : mulMap M N ∘ₗ (inclusion hN).lTensor M = mulMap M N'

--- 原说明 ---
If for any finitely generated submodules `N'` of `N`, `M` and `N'` are linearly 
disjoint,
then `M` and `N` themselves are linearly disjoint.
-/
theorem of_linearDisjoint_fg_right
    (H : ∀ N' : Submodule R S, N' ≤ N → N'.FG → M.LinearDisjoint N') :
    M.LinearDisjoint N := (linearDisjoint_iff _ _).2 fun x y hxy ↦ by
  obtain ⟨N', hN, hFG, h⟩ :=
    TensorProduct.exists_finite_submodule_right_of_setFinite' {x, y} (Set.toFinite _)
  rw [Module.Finite.iff_fg] at hFG
  obtain ⟨x', hx'⟩ := h (show x ∈ {x, y} by simp)
  obtain ⟨y', hy'⟩ := h (show y ∈ {x, y} by simp)
  rw [← hx', ← hy']; congr
  exact (H N' hN hFG).injective (by simp [← mulMap_comp_lTensor _ hN, hx', hy', hxy])

/-- If for any finitely generated submodules `M'` and `N'` of `M` and `N`, respectively,
`M'` and `N'` are linearly disjoint, then `M` and `N` themselves are linearly disjoint. -/
/-
**Submodule.LinearDisjoint.of_linearDisjoint_fg** 是 Mathlib 中的一个定理，位于命名空间 `Submo
dule.LinearDisjoint`。
形式化陈述：of_linearDisjoint_fg (H : forall (M' N' : Submodule R S), M' <= M -> N' <=
 N -> M'.FG -> N'.FG -> M'.LinearDisjoint N') : M.LinearDisjoint N
参数：H : forall (M' N' : Submodule R S), M' <= M -> N' <= N -> M'.FG -> N'.FG -> M
'.LinearDisjoint N'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.LinearDisjoint.of_linearDisjoint_fg_left`：of_linearDisjoint_fg
_left (H : forall M' : Submodule R S, M' <= M -> M'.FG -> M'.LinearDisjoint N) :
 M.LinearDisjoint N
· 使用定理 `Submodule.LinearDisjoint.of_linearDisjoint_fg_right`：of_linearDisjoint_f
g_right (H : forall N' : Submodule R S, N' <= N -> N'.FG -> M.LinearDisjoint N')
 : M.LinearDisjoint N

--- 原说明 ---
If for any finitely generated submodules `M'` and `N'` of `M` and `N`, respectiv
ely,
`M'` and `N'` are linearly disjoint, then `M` and `N` themselves are linearly di
sjoint.
-/
theorem of_linearDisjoint_fg
    (H : ∀ (M' N' : Submodule R S), M' ≤ M → N' ≤ N → M'.FG → N'.FG → M'.LinearDisjoint N') :
    M.LinearDisjoint N :=
  of_linearDisjoint_fg_left _ _ fun _ hM hM' ↦
    of_linearDisjoint_fg_right _ _ fun _ hN hN' ↦ H _ _ hM hN hM' hN'

end LinearDisjoint

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring S] [Algebra R S]

variable {M N : Submodule R S}

/-- Linear disjointness is symmetric in a commutative ring. -/
/-
**Submodule.LinearDisjoint.symm** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.LinearDisjo
int`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommSemiring R] [inst_1 : CommSemiring
 S] [inst_2 : Algebra R S]   {M N : Submodule R S}, M.LinearDisjoint N → N.Linea
rDisjoint M
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.LinearDisjoint.symm_of_commute`：∀ {R : Type u} {S : Type v} [i
nst : CommSemiring R] [inst_1 : Semiring S] [inst_2 : Algebra R S] {M N : Submod
ule R S},   M.LinearDisjoint N…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a

--- 原说明 ---
Linear disjointness is symmetric in a commutative ring.
-/
theorem LinearDisjoint.symm (H : M.LinearDisjoint N) : N.LinearDisjoint M :=
  H.symm_of_commute fun _ _ ↦ mul_comm _ _

/-- Linear disjointness is symmetric in a commutative ring. -/
/-
**Submodule.linearDisjoint_comm** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：linearDisjoint_comm : M.LinearDisjoint N ↔ N.LinearDisjoint M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.LinearDisjoint.symm`：∀ {R : Type u} {S : Type v} [inst : CommS
emiring R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S]   {M N : Submodule R
 S}, M.LinearDisjoi…

--- 原说明 ---
Linear disjointness is symmetric in a commutative ring.
-/
theorem linearDisjoint_comm : M.LinearDisjoint N ↔ N.LinearDisjoint M :=
  ⟨LinearDisjoint.symm, LinearDisjoint.symm⟩

end CommSemiring

section Ring

namespace LinearDisjoint

variable [CommRing R] [Ring S] [Algebra R S]

variable (M N : Submodule R S)

variable {M N} in
/-- If `M` and `N` are linearly disjoint, if `N` is a flat `R`-module, then for any family of
`R`-linearly independent elements `{ m_i }` of `M`, they are also `N`-linearly independent,
in the sense that the `R`-linear map from `ι →₀ N` to `S` which maps `{ n_i }`
to the sum of `m_i * n_i` (`Submodule.mulLeftMap N m`) has trivial kernel. -/
/-
**Submodule.LinearDisjoint.linearIndependent_left_of_flat** 是 Mathlib 中的一个定理，位于命
名空间 `Submodule.LinearDisjoint`。
形式化陈述：linearIndependent_left_of_flat (H : M.LinearDisjoint N) [Module.Flat R N] 
{ι : Type*} {m : ι -> M} (hm : LinearIndependent R m) : LinearMap.ker (mulLeftMa
p N m) = ⊥
参数：H : M.LinearDisjoint N；hm : LinearIndependent R m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ker_eq_bot_of_injective`：ker_eq_bot_of_injective {f : M ->ₛₗ[τ
₁₂] M₂} (hf : Injective f) : ker f = ⊥
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mulLeftMap_eq_mulMap_comp`：mulLeftMap_eq_mulMap_comp {ι : Type
*} [DecidableEq ι] (m : ι -> M) : mulLeftMap N m = mulMap M N ∘ₗ LinearMap.rTens
or N (Finsupp.linearCombi…
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Submodule.LinearDisjoint.injective`：∀ {R : Type u} {S : Type v} [inst : 
CommSemiring R] [inst_1 : Semiring S] [inst_2 : Algebra R S] {M N : Submodule R 
S},   M.LinearDisjoint N…
· 使用定理 `Module.Flat.rTensor_preserves_injective_linearMap`：rTensor_preserves_inj
ective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Function.Injective f) : Funct
ion.Injective (f.rTensor M)
· 使用定理 `LinearIndependent.eq_1`：∀ {ι : Type u'} (R : Type u_2) {M : Type u_4} (v
 : ι → M) [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Modu
le R M], Lin…

--- 原说明 ---
If `M` and `N` are linearly disjoint, if `N` is a flat `R`-module, then for any 
family of
`R`-linearly independent elements `{ m_i }` of `M`, they are also `N`-linearly i
ndependent,
in the sense that the `R`-linear map from `ι →₀ N` to `S` which maps `{ n_i }`
to the sum of `m_i * n_i` (`Submodule.mulLeftMap N m`) has trivial kernel.
-/
theorem linearIndependent_left_of_flat (H : M.LinearDisjoint N) [Module.Flat R N]
    {ι : Type*} {m : ι → M} (hm : LinearIndependent R m) : LinearMap.ker (mulLeftMap N m) = ⊥ := by
  refine LinearMap.ker_eq_bot_of_injective ?_
  classical simp_rw [mulLeftMap_eq_mulMap_comp, LinearMap.coe_comp, LinearEquiv.coe_coe,
    ← Function.comp_assoc, EquivLike.injective_comp]
  rw [LinearIndependent] at hm
  exact H.injective.comp (Module.Flat.rTensor_preserves_injective_linearMap (M := N) _ hm)

/-- If `{ m_i }` is an `R`-basis of `M`, which is also `N`-linearly independent,
then `M` and `N` are linearly disjoint. -/
/-
**Submodule.LinearDisjoint.of_basis_left** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.Li
nearDisjoint`。
形式化陈述：of_basis_left {ι : Type*} (m : Basis ι R M) (H : LinearMap.ker (mulLeftMap
 N m) = ⊥) : M.LinearDisjoint N
参数：m : Basis ι R M；H : LinearMap.ker (mulLeftMap N m) = ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Submodule.LinearDisjoint.of_basis_left'`：of_basis_left' {ι : Type*} (m :
 Basis ι R M) (H : Function.Injective (mulLeftMap N m)) : M.LinearDisjoint N
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f

--- 原说明 ---
If `{ m_i }` is an `R`-basis of `M`, which is also `N`-linearly independent,
then `M` and `N` are linearly disjoint.
-/
theorem of_basis_left {ι : Type*} (m : Basis ι R M)
    (H : LinearMap.ker (mulLeftMap N m) = ⊥) : M.LinearDisjoint N :=
  of_basis_left' M N m (LinearMap.ker_eq_bot.1 H)

variable {M N} in
/-- If `M` and `N` are linearly disjoint, if `M` is a flat `R`-module, then for any family of
`R`-linearly independent elements `{ n_i }` of `N`, they are also `M`-linearly independent,
in the sense that the `R`-linear map from `ι →₀ M` to `S` which maps `{ m_i }`
to the sum of `m_i * n_i` (`Submodule.mulRightMap M n`) has trivial kernel. -/
/-
**Submodule.LinearDisjoint.linearIndependent_right_of_flat** 是 Mathlib 中的一个定理，位于
命名空间 `Submodule.LinearDisjoint`。
形式化陈述：linearIndependent_right_of_flat (H : M.LinearDisjoint N) [Module.Flat R M]
 {ι : Type*} {n : ι -> N} (hn : LinearIndependent R n) : LinearMap.ker (mulRight
Map M n) = ⊥
参数：H : M.LinearDisjoint N；hn : LinearIndependent R n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ker_eq_bot_of_injective`：ker_eq_bot_of_injective {f : M ->ₛₗ[τ
₁₂] M₂} (hf : Injective f) : ker f = ⊥
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mulRightMap_eq_mulMap_comp`：mulRightMap_eq_mulMap_comp {ι : Ty
pe*} [DecidableEq ι] (n : ι -> N) : mulRightMap M n = mulMap M N ∘ₗ LinearMap.lT
ensor M (Finsupp.linearCom…
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Submodule.LinearDisjoint.injective`：∀ {R : Type u} {S : Type v} [inst : 
CommSemiring R] [inst_1 : Semiring S] [inst_2 : Algebra R S] {M N : Submodule R 
S},   M.LinearDisjoint N…
· 使用定理 `Module.Flat.lTensor_preserves_injective_linearMap`：lTensor_preserves_inj
ective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Function.Injective f) : Funct
ion.Injective (f.lTensor M)
· 使用定理 `LinearIndependent.eq_1`：∀ {ι : Type u'} (R : Type u_2) {M : Type u_4} (v
 : ι → M) [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Modu
le R M], Lin…

--- 原说明 ---
If `M` and `N` are linearly disjoint, if `M` is a flat `R`-module, then for any 
family of
`R`-linearly independent elements `{ n_i }` of `N`, they are also `M`-linearly i
ndependent,
in the sense that the `R`-linear map from `ι →₀ M` to `S` which maps `{ m_i }`
to the sum of `m_i * n_i` (`Submodule.mulRightMap M n`) has trivial kernel.
-/
theorem linearIndependent_right_of_flat (H : M.LinearDisjoint N) [Module.Flat R M]
    {ι : Type*} {n : ι → N} (hn : LinearIndependent R n) : LinearMap.ker (mulRightMap M n) = ⊥ := by
  refine LinearMap.ker_eq_bot_of_injective ?_
  classical simp_rw [mulRightMap_eq_mulMap_comp, LinearMap.coe_comp, LinearEquiv.coe_coe,
    ← Function.comp_assoc, EquivLike.injective_comp]
  rw [LinearIndependent] at hn
  exact H.injective.comp (Module.Flat.lTensor_preserves_injective_linearMap (M := M) _ hn)

/-- If `{ n_i }` is an `R`-basis of `N`, which is also `M`-linearly independent,
then `M` and `N` are linearly disjoint. -/
/-
**Submodule.LinearDisjoint.of_basis_right** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.L
inearDisjoint`。
形式化陈述：of_basis_right {ι : Type*} (n : Basis ι R N) (H : LinearMap.ker (mulRightM
ap M n) = ⊥) : M.LinearDisjoint N
参数：n : Basis ι R N；H : LinearMap.ker (mulRightMap M n) = ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Submodule.LinearDisjoint.of_basis_right'`：of_basis_right' {ι : Type*} (n
 : Basis ι R N) (H : Function.Injective (mulRightMap M n)) : M.LinearDisjoint N
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f

--- 原说明 ---
If `{ n_i }` is an `R`-basis of `N`, which is also `M`-linearly independent,
then `M` and `N` are linearly disjoint.
-/
theorem of_basis_right {ι : Type*} (n : Basis ι R N)
    (H : LinearMap.ker (mulRightMap M n) = ⊥) : M.LinearDisjoint N :=
  of_basis_right' M N n (LinearMap.ker_eq_bot.1 H)

variable {M N} in
/-- If `M` and `N` are linearly disjoint, if `M` is flat, then for any family of
`R`-linearly independent elements `{ m_i }` of `M`, and any family of
`R`-linearly independent elements `{ n_j }` of `N`, the family `{ m_i * n_j }` in `S` is
also `R`-linearly independent. -/
/-
**Submodule.LinearDisjoint.linearIndependent_mul_of_flat_left** 是 Mathlib 中的一个定理
，位于命名空间 `Submodule.LinearDisjoint`。
形式化陈述：linearIndependent_mul_of_flat_left (H : M.LinearDisjoint N) [Module.Flat R
 M] {κ ι : Type*} {m : κ -> M} {n : ι -> N} (hm : LinearIndependent R m) (hn : L
inearIndependent R n) : LinearIndependent R fun (i : κ × ι) => (m i.1).1 * (n i.
2).1
参数：H : M.LinearDisjoint N；hm : LinearIndependent R m；hn : LinearIndependent R n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearIndependent.eq_1`：∀ {ι : Type u'} (R : Type u_2) {M : Type u_4} (v
 : ι → M) [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Modu
le R M], Lin…
· 使用定理 `Module.Flat.rTensor_preserves_injective_linearMap`：rTensor_preserves_inj
ective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Function.Injective f) : Funct
ion.Injective (f.rTensor M)
· 使用定理 `Module.Flat.lTensor_preserves_injective_linearMap`：lTensor_preserves_inj
ective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Function.Injective f) : Funct
ion.Injective (f.lTensor M)
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Submodule.LinearDisjoint.injective`：∀ {R : Type u} {S : Type v} [inst : 
CommSemiring R] [inst_1 : Semiring S] [inst_2 : Algebra R S] {M N : Submodule R 
S},   M.LinearDisjoint N…
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Finsupp.lhom_ext'`：lhom_ext' ⦃φ ψ : (α ->₀ M) ->ₛₗ[σ₁₂] N⦄ (h : forall a
, φ.comp (lsingle a) = ψ.comp (lsingle a)) : φ = ψ
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `finsuppTensorFinsupp'_symm_single_eq_single_one_tmul`：∀ (R : Type u_1) (
ι : Type u_5) (κ : Type u_6) [inst : CommSemiring R] (i : ι × κ) (r : R),   ((fi
nsuppTensorFinsupp' R ι κ).symm fun₀ | i =…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `M` and `N` are linearly disjoint, if `M` is flat, then for any family of
`R`-linearly independent elements `{ m_i }` of `M`, and any family of
`R`-linearly independent elements `{ n_j }` of `N`, the family `{ m_i * n_j }` i
n `S` is
also `R`-linearly independent.
-/
theorem linearIndependent_mul_of_flat_left (H : M.LinearDisjoint N) [Module.Flat R M]
    {κ ι : Type*} {m : κ → M} {n : ι → N} (hm : LinearIndependent R m)
    (hn : LinearIndependent R n) : LinearIndependent R fun (i : κ × ι) ↦ (m i.1).1 * (n i.2).1 := by
  rw [LinearIndependent] at hm hn ⊢
  let i0 := (finsuppTensorFinsupp' R κ ι).symm
  let i1 := LinearMap.rTensor (ι →₀ R) (Finsupp.linearCombination R m)
  let i2 := LinearMap.lTensor M (Finsupp.linearCombination R n)
  let i := mulMap M N ∘ₗ i2 ∘ₗ i1 ∘ₗ i0.toLinearMap
  have h1 : Function.Injective i1 := Module.Flat.rTensor_preserves_injective_linearMap _ hm
  have h2 : Function.Injective i2 := Module.Flat.lTensor_preserves_injective_linearMap _ hn
  have h : Function.Injective i := H.injective.comp h2 |>.comp h1 |>.comp i0.injective
  have : i = Finsupp.linearCombination R fun i ↦ (m i.1).1 * (n i.2).1 := by
    ext x
    simp [i, i0, i1, i2, finsuppTensorFinsupp'_symm_single_eq_single_one_tmul]
  rwa [this] at h

variable {M N} in
/-- If `M` and `N` are linearly disjoint, if `N` is flat, then for any family of
`R`-linearly independent elements `{ m_i }` of `M`, and any family of
`R`-linearly independent elements `{ n_j }` of `N`, the family `{ m_i * n_j }` in `S` is
also `R`-linearly independent. -/
/-
**Submodule.LinearDisjoint.linearIndependent_mul_of_flat_right** 是 Mathlib 中的一个定
理，位于命名空间 `Submodule.LinearDisjoint`。
形式化陈述：linearIndependent_mul_of_flat_right (H : M.LinearDisjoint N) [Module.Flat 
R N] {κ ι : Type*} {m : κ -> M} {n : ι -> N} (hm : LinearIndependent R m) (hn : 
LinearIndependent R n) : LinearIndependent R fun (i : κ × ι) => (m i.1).1 * (n i
.2).1
参数：H : M.LinearDisjoint N；hm : LinearIndependent R m；hn : LinearIndependent R n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearIndependent.eq_1`：∀ {ι : Type u'} (R : Type u_2) {M : Type u_4} (v
 : ι → M) [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Modu
le R M], Lin…
· 使用定理 `Module.Flat.lTensor_preserves_injective_linearMap`：lTensor_preserves_inj
ective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Function.Injective f) : Funct
ion.Injective (f.lTensor M)
· 使用定理 `Module.Flat.rTensor_preserves_injective_linearMap`：rTensor_preserves_inj
ective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Function.Injective f) : Funct
ion.Injective (f.rTensor M)
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Submodule.LinearDisjoint.injective`：∀ {R : Type u} {S : Type v} [inst : 
CommSemiring R] [inst_1 : Semiring S] [inst_2 : Algebra R S] {M N : Submodule R 
S},   M.LinearDisjoint N…
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Finsupp.lhom_ext'`：lhom_ext' ⦃φ ψ : (α ->₀ M) ->ₛₗ[σ₁₂] N⦄ (h : forall a
, φ.comp (lsingle a) = ψ.comp (lsingle a)) : φ = ψ
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `finsuppTensorFinsupp'_symm_single_eq_single_one_tmul`：∀ (R : Type u_1) (
ι : Type u_5) (κ : Type u_6) [inst : CommSemiring R] (i : ι × κ) (r : R),   ((fi
nsuppTensorFinsupp' R ι κ).symm fun₀ | i =…
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `M` and `N` are linearly disjoint, if `N` is flat, then for any family of
`R`-linearly independent elements `{ m_i }` of `M`, and any family of
`R`-linearly independent elements `{ n_j }` of `N`, the family `{ m_i * n_j }` i
n `S` is
also `R`-linearly independent.
-/
theorem linearIndependent_mul_of_flat_right (H : M.LinearDisjoint N) [Module.Flat R N]
    {κ ι : Type*} {m : κ → M} {n : ι → N} (hm : LinearIndependent R m)
    (hn : LinearIndependent R n) : LinearIndependent R fun (i : κ × ι) ↦ (m i.1).1 * (n i.2).1 := by
  rw [LinearIndependent] at hm hn ⊢
  let i0 := (finsuppTensorFinsupp' R κ ι).symm
  let i1 := LinearMap.lTensor (κ →₀ R) (Finsupp.linearCombination R n)
  let i2 := LinearMap.rTensor N (Finsupp.linearCombination R m)
  let i := mulMap M N ∘ₗ i2 ∘ₗ i1 ∘ₗ i0.toLinearMap
  have h1 : Function.Injective i1 := Module.Flat.lTensor_preserves_injective_linearMap _ hn
  have h2 : Function.Injective i2 := Module.Flat.rTensor_preserves_injective_linearMap _ hm
  have h : Function.Injective i := H.injective.comp h2 |>.comp h1 |>.comp i0.injective
  have : i = Finsupp.linearCombination R fun i ↦ (m i.1).1 * (n i.2).1 := by
    ext x
    simp [i, i0, i1, i2, finsuppTensorFinsupp'_symm_single_eq_single_one_tmul]
  rwa [this] at h

variable {M N} in
/-- If `M` and `N` are linearly disjoint, if one of `M` and `N` is flat, then for any family of
`R`-linearly independent elements `{ m_i }` of `M`, and any family of
`R`-linearly independent elements `{ n_j }` of `N`, the family `{ m_i * n_j }` in `S` is
also `R`-linearly independent. -/
/-
**Submodule.LinearDisjoint.linearIndependent_mul_of_flat** 是 Mathlib 中的一个定理，位于命名
空间 `Submodule.LinearDisjoint`。
形式化陈述：linearIndependent_mul_of_flat (H : M.LinearDisjoint N) (hf : Module.Flat R
 M ∨ Module.Flat R N) {κ ι : Type*} {m : κ -> M} {n : ι -> N} (hm : LinearIndepe
ndent R m) (hn : LinearIndependent R n) : LinearIndependent R fun (i : κ × ι) =>
 (m i.1).1 * (n i.2).1
参数：H : M.LinearDisjoint N；hf : Module.Flat R M ∨ Module.Flat R N；hm : LinearInde
pendent R m；hn : LinearIndependent R n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.LinearDisjoint.linearIndependent_mul_of_flat_left`：linearIndep
endent_mul_of_flat_left (H : M.LinearDisjoint N) [Module.Flat R M] {κ ι : Type*}
 {m : κ -> M} {n : ι -> N} (hm : LinearIndependen…
· 使用定理 `Submodule.LinearDisjoint.linearIndependent_mul_of_flat_right`：linearInde
pendent_mul_of_flat_right (H : M.LinearDisjoint N) [Module.Flat R N] {κ ι : Type
*} {m : κ -> M} {n : ι -> N} (hm : LinearIndepende…

--- 原说明 ---
If `M` and `N` are linearly disjoint, if one of `M` and `N` is flat, then for an
y family of
`R`-linearly independent elements `{ m_i }` of `M`, and any family of
`R`-linearly independent elements `{ n_j }` of `N`, the family `{ m_i * n_j }` i
n `S` is
also `R`-linearly independent.
-/
theorem linearIndependent_mul_of_flat (H : M.LinearDisjoint N)
    (hf : Module.Flat R M ∨ Module.Flat R N)
    {κ ι : Type*} {m : κ → M} {n : ι → N} (hm : LinearIndependent R m)
    (hn : LinearIndependent R n) : LinearIndependent R fun (i : κ × ι) ↦ (m i.1).1 * (n i.2).1 := by
  rcases hf with _ | _
  · exact H.linearIndependent_mul_of_flat_left hm hn
  · exact H.linearIndependent_mul_of_flat_right hm hn

/-- If `{ m_i }` is an `R`-basis of `M`, if `{ n_j }` is an `R`-basis of `N`,
such that the family `{ m_i * n_j }` in `S` is `R`-linearly independent,
then `M` and `N` are linearly disjoint. -/
/-
**Submodule.LinearDisjoint.of_basis_mul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.Lin
earDisjoint`。
形式化陈述：of_basis_mul {κ ι : Type*} (m : Basis κ R M) (n : Basis ι R N) (H : Linear
Independent R fun (i : κ × ι) => (m i.1).1 * (n i.2).1) : M.LinearDisjoint N
参数：m : Basis κ R M；n : Basis ι R N；H : LinearIndependent R fun (i : κ × ι) => (m
 i.1).1 * (n i.2).1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.LinearDisjoint.of_basis_mul'`：of_basis_mul' {κ ι : Type*} (m :
 Basis κ R M) (n : Basis ι R N) (H : Function.Injective (Finsupp.linearCombinati
on R fun i : κ × ι => (m i.1…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearIndependent.eq_1`：∀ {ι : Type u'} (R : Type u_2) {M : Type u_4} (v
 : ι → M) [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Modu
le R M], Lin…

--- 原说明 ---
If `{ m_i }` is an `R`-basis of `M`, if `{ n_j }` is an `R`-basis of `N`,
such that the family `{ m_i * n_j }` in `S` is `R`-linearly independent,
then `M` and `N` are linearly disjoint.
-/
theorem of_basis_mul {κ ι : Type*} (m : Basis κ R M) (n : Basis ι R N)
    (H : LinearIndependent R fun (i : κ × ι) ↦ (m i.1).1 * (n i.2).1) : M.LinearDisjoint N := by
  rw [LinearIndependent] at H
  exact of_basis_mul' M N m n H

variable {M N} in
/-- If `M` and `N` are linearly disjoint, if `N` is flat, then for any submodule `M'` of `M`,
`M'` and `N` are also linearly disjoint. -/
/-
**Submodule.LinearDisjoint.of_le_left_of_flat** 是 Mathlib 中的一个定理，位于命名空间 `Submodu
le.LinearDisjoint`。
形式化陈述：of_le_left_of_flat (H : M.LinearDisjoint N) {M' : Submodule R S} (h : M' <
= M) [Module.Flat R N] : M'.LinearDisjoint N
参数：H : M.LinearDisjoint N；h : M' <= M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Submodule.LinearDisjoint.injective`：∀ {R : Type u} {S : Type v} [inst : 
CommSemiring R] [inst_1 : Semiring S] [inst_2 : Algebra R S] {M N : Submodule R 
S},   M.LinearDisjoint N…
· 使用定理 `Module.Flat.rTensor_preserves_injective_linearMap`：rTensor_preserves_inj
ective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Function.Injective f) : Funct
ion.Injective (f.rTensor M)
· 使用定理 `Submodule.inclusion_injective`：inclusion_injective (h : p <= p') : Funct
ion.Injective (inclusion h)
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `M` and `N` are linearly disjoint, if `N` is flat, then for any submodule `M'
` of `M`,
`M'` and `N` are also linearly disjoint.
-/
theorem of_le_left_of_flat (H : M.LinearDisjoint N) {M' : Submodule R S}
    (h : M' ≤ M) [Module.Flat R N] : M'.LinearDisjoint N := by
  let i := mulMap M N ∘ₗ (inclusion h).rTensor N
  have hi : Function.Injective i := H.injective.comp <|
    Module.Flat.rTensor_preserves_injective_linearMap _ <| inclusion_injective h
  have : i = mulMap M' N := by ext; simp [i]
  exact ⟨this ▸ hi⟩

variable {M N} in
/-- If `M` and `N` are linearly disjoint, if `M` is flat, then for any submodule `N'` of `N`,
`M` and `N'` are also linearly disjoint. -/
/-
**Submodule.LinearDisjoint.of_le_right_of_flat** 是 Mathlib 中的一个定理，位于命名空间 `Submod
ule.LinearDisjoint`。
形式化陈述：of_le_right_of_flat (H : M.LinearDisjoint N) {N' : Submodule R S} (h : N' 
<= N) [Module.Flat R M] : M.LinearDisjoint N'
参数：H : M.LinearDisjoint N；h : N' <= N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Submodule.LinearDisjoint.injective`：∀ {R : Type u} {S : Type v} [inst : 
CommSemiring R] [inst_1 : Semiring S] [inst_2 : Algebra R S] {M N : Submodule R 
S},   M.LinearDisjoint N…
· 使用定理 `Module.Flat.lTensor_preserves_injective_linearMap`：lTensor_preserves_inj
ective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Function.Injective f) : Funct
ion.Injective (f.lTensor M)
· 使用定理 `Submodule.inclusion_injective`：inclusion_injective (h : p <= p') : Funct
ion.Injective (inclusion h)
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `M` and `N` are linearly disjoint, if `M` is flat, then for any submodule `N'
` of `N`,
`M` and `N'` are also linearly disjoint.
-/
theorem of_le_right_of_flat (H : M.LinearDisjoint N) {N' : Submodule R S}
    (h : N' ≤ N) [Module.Flat R M] : M.LinearDisjoint N' := by
  let i := mulMap M N ∘ₗ (inclusion h).lTensor M
  have hi : Function.Injective i := H.injective.comp <|
    Module.Flat.lTensor_preserves_injective_linearMap _ <| inclusion_injective h
  have : i = mulMap M N' := by ext; simp [i]
  exact ⟨this ▸ hi⟩

variable {M N} in
/-- If `M` and `N` are linearly disjoint, `M'` and `N'` are submodules of `M` and `N`,
respectively, such that `N` and `M'` are flat, then `M'` and `N'` are also linearly disjoint. -/
/-
**Submodule.LinearDisjoint.of_le_of_flat_right** 是 Mathlib 中的一个定理，位于命名空间 `Submod
ule.LinearDisjoint`。
形式化陈述：of_le_of_flat_right (H : M.LinearDisjoint N) {M' N' : Submodule R S} (hm :
 M' <= M) (hn : N' <= N) [Module.Flat R N] [Module.Flat R M'] : M'.LinearDisjoin
t N'
参数：H : M.LinearDisjoint N；hm : M' <= M；hn : N' <= N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.LinearDisjoint.of_le_right_of_flat`：of_le_right_of_flat (H : M
.LinearDisjoint N) {N' : Submodule R S} (h : N' <= N) [Module.Flat R M] : M.Line
arDisjoint N'
· 使用定理 `Submodule.LinearDisjoint.of_le_left_of_flat`：of_le_left_of_flat (H : M.L
inearDisjoint N) {M' : Submodule R S} (h : M' <= M) [Module.Flat R N] : M'.Linea
rDisjoint N

--- 原说明 ---
If `M` and `N` are linearly disjoint, `M'` and `N'` are submodules of `M` and `N
`,
respectively, such that `N` and `M'` are flat, then `M'` and `N'` are also linea
rly disjoint.
-/
theorem of_le_of_flat_right (H : M.LinearDisjoint N) {M' N' : Submodule R S}
    (hm : M' ≤ M) (hn : N' ≤ N) [Module.Flat R N] [Module.Flat R M'] :
    M'.LinearDisjoint N' := (H.of_le_left_of_flat hm).of_le_right_of_flat hn

variable {M N} in
/-- If `M` and `N` are linearly disjoint, `M'` and `N'` are submodules of `M` and `N`,
respectively, such that `M` and `N'` are flat, then `M'` and `N'` are also linearly disjoint. -/
/-
**Submodule.LinearDisjoint.of_le_of_flat_left** 是 Mathlib 中的一个定理，位于命名空间 `Submodu
le.LinearDisjoint`。
形式化陈述：of_le_of_flat_left (H : M.LinearDisjoint N) {M' N' : Submodule R S} (hm : 
M' <= M) (hn : N' <= N) [Module.Flat R M] [Module.Flat R N'] : M'.LinearDisjoint
 N'
参数：H : M.LinearDisjoint N；hm : M' <= M；hn : N' <= N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.LinearDisjoint.of_le_left_of_flat`：of_le_left_of_flat (H : M.L
inearDisjoint N) {M' : Submodule R S} (h : M' <= M) [Module.Flat R N] : M'.Linea
rDisjoint N
· 使用定理 `Submodule.LinearDisjoint.of_le_right_of_flat`：of_le_right_of_flat (H : M
.LinearDisjoint N) {N' : Submodule R S} (h : N' <= N) [Module.Flat R M] : M.Line
arDisjoint N'

--- 原说明 ---
If `M` and `N` are linearly disjoint, `M'` and `N'` are submodules of `M` and `N
`,
respectively, such that `M` and `N'` are flat, then `M'` and `N'` are also linea
rly disjoint.
-/
theorem of_le_of_flat_left (H : M.LinearDisjoint N) {M' N' : Submodule R S}
    (hm : M' ≤ M) (hn : N' ≤ N) [Module.Flat R M] [Module.Flat R N'] :
    M'.LinearDisjoint N' := (H.of_le_right_of_flat hn).of_le_left_of_flat hm

/-- If `N` is flat, `M` is contained in `i(R)`, where `i : R → S` is the structure map,
then `M` and `N` are linearly disjoint. -/
/-
**Submodule.LinearDisjoint.of_left_le_one_of_flat** 是 Mathlib 中的一个定理，位于命名空间 `Sub
module.LinearDisjoint`。
形式化陈述：of_left_le_one_of_flat (h : M <= 1) [Module.Flat R N] : M.LinearDisjoint N
参数：h : M <= 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.LinearDisjoint.of_le_left_of_flat`：of_le_left_of_flat (H : M.L
inearDisjoint N) {M' : Submodule R S} (h : M' <= M) [Module.Flat R N] : M'.Linea
rDisjoint N
· 使用定理 `Submodule.LinearDisjoint.one_left`：one_left : (1 : Submodule R S).Linear
Disjoint N

--- 原说明 ---
If `N` is flat, `M` is contained in `i(R)`, where `i : R → S` is the structure m
ap,
then `M` and `N` are linearly disjoint.
-/
theorem of_left_le_one_of_flat (h : M ≤ 1) [Module.Flat R N] :
    M.LinearDisjoint N := (one_left N).of_le_left_of_flat h

/-- If `M` is flat, `N` is contained in `i(R)`, where `i : R → S` is the structure map,
then `M` and `N` are linearly disjoint. -/
/-
**Submodule.LinearDisjoint.of_right_le_one_of_flat** 是 Mathlib 中的一个定理，位于命名空间 `Su
bmodule.LinearDisjoint`。
形式化陈述：of_right_le_one_of_flat (h : N <= 1) [Module.Flat R M] : M.LinearDisjoint 
N
参数：h : N <= 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.LinearDisjoint.of_le_right_of_flat`：of_le_right_of_flat (H : M
.LinearDisjoint N) {N' : Submodule R S} (h : N' <= N) [Module.Flat R M] : M.Line
arDisjoint N'
· 使用定理 `Submodule.LinearDisjoint.one_right`：one_right : M.LinearDisjoint (1 : Su
bmodule R S)

--- 原说明 ---
If `M` is flat, `N` is contained in `i(R)`, where `i : R → S` is the structure m
ap,
then `M` and `N` are linearly disjoint.
-/
theorem of_right_le_one_of_flat (h : N ≤ 1) [Module.Flat R M] :
    M.LinearDisjoint N := (one_right M).of_le_right_of_flat h

section not_linearIndependent_pair

variable {M N}

section
variable (H : M.LinearDisjoint N)
include H

section

variable [Nontrivial R]

/-- If `M` and `N` are linearly disjoint, if `M` is flat, then any two commutative
elements of `↥(M ⊓ N)` are not `R`-linearly independent (namely, their span is not `R ^ 2`). -/
/-
**Submodule.LinearDisjoint.not_linearIndependent_pair_of_commute_of_flat_left** 
是 Mathlib 中的一个定理，位于命名空间 `Submodule.LinearDisjoint`。
形式化陈述：not_linearIndependent_pair_of_commute_of_flat_left [Module.Flat R M] (a b 
: ↥(M ⊓ N)) (hc : Commute a.1 b.1) : ¬LinearIndependent R ![a, b]
参数：a b : ↥(M ⊓ N)；hc : Commute a.1 b.1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `LinearIndependent.map'`：LinearIndependent.map' (hv : LinearIndependent R
 v) (f : M ->ₗ[R] M') (hf_inj : LinearMap.ker f = ⊥) : LinearIndependent R (f ∘ 
v)
· 使用定理 `Submodule.ker_inclusion`：ker_inclusion (p p' : Submodule R M) (h : p <= 
p') : ker (inclusion h) = ⊥
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Submodule.mulRightMap_apply_single`：mulRightMap_apply_single {M N : Subm
odule R S} {ι : Type*} (n : ι -> N) (i : ι) (m : M) : mulRightMap M n (Finsupp.s
ingle i m) = m.1 * (n i)…
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearIndependent.ne_zero`：LinearIndependent.ne_zero [Nontrivial R] (i :
 ι) (hv : LinearIndependent R v) : v i != 0
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `ZeroMemClass.coe_eq_zero`：∀ {A : Type u_3} {M₁ : Type u_4} [inst : SetLi
ke A M₁] [inst_1 : Zero M₁] [hA : ZeroMemClass A M₁] {S' : A} {x : ↥S'},   ↑x = 
0 ↔ x = 0
· 使用定理 `AddSubmonoid.mk_eq_zero`：∀ {M : Type u_4} [inst : AddZeroClass M] (S : A
ddSubmonoid M) {a : M} {ha : a ∈ S}, ⟨a, ha⟩ = 0 ↔ a = 0
· 使用定理 `Fin.instNeZeroHAddNatOfNat_mathlib_1`：∀ (n : ℕ) [NeZero n], NeZero 1
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Submodule.mem_bot`：mem_bot {x : M} : x in (⊥ : Submodule R M) ↔ x = 0
· 使用定理 `Submodule.LinearDisjoint.linearIndependent_right_of_flat`：linearIndepend
ent_right_of_flat (H : M.LinearDisjoint N) [Module.Flat R M] {ι : Type*} {n : ι 
-> N} (hn : LinearIndependent R n) : LinearMap…
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
If `M` and `N` are linearly disjoint, if `M` is flat, then any two commutative
elements of `↥(M ⊓ N)` are not `R`-linearly independent (namely, their span is n
ot `R ^ 2`).
-/
theorem not_linearIndependent_pair_of_commute_of_flat_left [Module.Flat R M]
    (a b : ↥(M ⊓ N)) (hc : Commute a.1 b.1) : ¬LinearIndependent R ![a, b] := fun h ↦ by
  let n : Fin 2 → N := (inclusion inf_le_right) ∘ ![a, b]
  have hn : LinearIndependent R n := h.map' _ (ker_inclusion _ _ _)
  -- need this instance otherwise it only has semigroup structure
  let : AddCommGroup (Fin 2 →₀ M) := Finsupp.instAddCommGroup
  let m : Fin 2 →₀ M := .single 0 ⟨b.1, b.2.1⟩ - .single 1 ⟨a.1, a.2.1⟩
  have hm : mulRightMap M n m = 0 := by simp [m, n, show _ * _ = _ * _ from hc]
  rw [← LinearMap.mem_ker, H.linearIndependent_right_of_flat hn, mem_bot] at hm
  simp only [Fin.isValue, sub_eq_zero, Finsupp.single_eq_single_iff, zero_ne_one, Subtype.mk.injEq,
    SetLike.coe_eq_coe, false_and, false_or, m] at hm
  repeat rw [AddSubmonoid.mk_eq_zero, ZeroMemClass.coe_eq_zero] at hm
  exact h.ne_zero 0 hm.2

/-- If `M` and `N` are linearly disjoint, if `N` is flat, then any two commutative
elements of `↥(M ⊓ N)` are not `R`-linearly independent (namely, their span is not `R ^ 2`). -/
/-
**Submodule.LinearDisjoint.not_linearIndependent_pair_of_commute_of_flat_right**
 是 Mathlib 中的一个定理，位于命名空间 `Submodule.LinearDisjoint`。
形式化陈述：not_linearIndependent_pair_of_commute_of_flat_right [Module.Flat R N] (a b
 : ↥(M ⊓ N)) (hc : Commute a.1 b.1) : ¬LinearIndependent R ![a, b]
参数：a b : ↥(M ⊓ N)；hc : Commute a.1 b.1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `LinearIndependent.map'`：LinearIndependent.map' (hv : LinearIndependent R
 v) (f : M ->ₗ[R] M') (hf_inj : LinearMap.ker f = ⊥) : LinearIndependent R (f ∘ 
v)
· 使用定理 `Submodule.ker_inclusion`：ker_inclusion (p p' : Submodule R M) (h : p <= 
p') : ker (inclusion h) = ⊥
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Submodule.mulLeftMap_apply_single`：mulLeftMap_apply_single {M N : Submod
ule R S} {ι : Type*} (m : ι -> M) (i : ι) (n : N) : mulLeftMap N m (Finsupp.sing
le i n) = (m i).1 * n.1
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearIndependent.ne_zero`：LinearIndependent.ne_zero [Nontrivial R] (i :
 ι) (hv : LinearIndependent R v) : v i != 0
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `ZeroMemClass.coe_eq_zero`：∀ {A : Type u_3} {M₁ : Type u_4} [inst : SetLi
ke A M₁] [inst_1 : Zero M₁] [hA : ZeroMemClass A M₁] {S' : A} {x : ↥S'},   ↑x = 
0 ↔ x = 0
· 使用定理 `AddSubmonoid.mk_eq_zero`：∀ {M : Type u_4} [inst : AddZeroClass M] (S : A
ddSubmonoid M) {a : M} {ha : a ∈ S}, ⟨a, ha⟩ = 0 ↔ a = 0
· 使用定理 `Fin.instNeZeroHAddNatOfNat_mathlib_1`：∀ (n : ℕ) [NeZero n], NeZero 1
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Submodule.mem_bot`：mem_bot {x : M} : x in (⊥ : Submodule R M) ↔ x = 0
· 使用定理 `Submodule.LinearDisjoint.linearIndependent_left_of_flat`：linearIndepende
nt_left_of_flat (H : M.LinearDisjoint N) [Module.Flat R N] {ι : Type*} {m : ι ->
 M} (hm : LinearIndependent R m) : LinearMap.…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
If `M` and `N` are linearly disjoint, if `N` is flat, then any two commutative
elements of `↥(M ⊓ N)` are not `R`-linearly independent (namely, their span is n
ot `R ^ 2`).
-/
theorem not_linearIndependent_pair_of_commute_of_flat_right [Module.Flat R N]
    (a b : ↥(M ⊓ N)) (hc : Commute a.1 b.1) : ¬LinearIndependent R ![a, b] := fun h ↦ by
  let m : Fin 2 → M := (inclusion inf_le_left) ∘ ![a, b]
  have hm : LinearIndependent R m := h.map' _ (ker_inclusion _ _ _)
  -- need this instance otherwise it only has semigroup structure
  let : AddCommGroup (Fin 2 →₀ N) := Finsupp.instAddCommGroup
  let n : Fin 2 →₀ N := .single 0 ⟨b.1, b.2.2⟩ - .single 1 ⟨a.1, a.2.2⟩
  have hn : mulLeftMap N m n = 0 := by simp [m, n, show _ * _ = _ * _ from hc]
  rw [← LinearMap.mem_ker, H.linearIndependent_left_of_flat hm, mem_bot] at hn
  simp only [Fin.isValue, sub_eq_zero, Finsupp.single_eq_single_iff, zero_ne_one, Subtype.mk.injEq,
    SetLike.coe_eq_coe, false_and, false_or, n] at hn
  repeat rw [AddSubmonoid.mk_eq_zero, ZeroMemClass.coe_eq_zero] at hn
  exact h.ne_zero 0 hn.2

/-- If `M` and `N` are linearly disjoint, if one of `M` and `N` is flat, then any two commutative
elements of `↥(M ⊓ N)` are not `R`-linearly independent (namely, their span is not `R ^ 2`). -/
/-
**Submodule.LinearDisjoint.not_linearIndependent_pair_of_commute_of_flat** 是 Mat
hlib 中的一个定理，位于命名空间 `Submodule.LinearDisjoint`。
形式化陈述：not_linearIndependent_pair_of_commute_of_flat (hf : Module.Flat R M ∨ Modu
le.Flat R N) (a b : ↥(M ⊓ N)) (hc : Commute a.1 b.1) : ¬LinearIndependent R ![a,
 b]
参数：hf : Module.Flat R M ∨ Module.Flat R N；a b : ↥(M ⊓ N)；hc : Commute a.1 b.1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.LinearDisjoint.not_linearIndependent_pair_of_commute_of_flat_l
eft`：not_linearIndependent_pair_of_commute_of_flat_left [Module.Flat R M] (a b :
 ↥(M ⊓ N)) (hc : Commute a.1 b.1) : ¬LinearIndependent R ![a, b]
· 使用定理 `Submodule.LinearDisjoint.not_linearIndependent_pair_of_commute_of_flat_r
ight`：not_linearIndependent_pair_of_commute_of_flat_right [Module.Flat R N] (a b
 : ↥(M ⊓ N)) (hc : Commute a.1 b.1) : ¬LinearIndependent R ![a, b]

--- 原说明 ---
If `M` and `N` are linearly disjoint, if one of `M` and `N` is flat, then any tw
o commutative
elements of `↥(M ⊓ N)` are not `R`-linearly independent (namely, their span is n
ot `R ^ 2`).
-/
theorem not_linearIndependent_pair_of_commute_of_flat (hf : Module.Flat R M ∨ Module.Flat R N)
    (a b : ↥(M ⊓ N)) (hc : Commute a.1 b.1) : ¬LinearIndependent R ![a, b] := by
  rcases hf with _ | _
  · exact H.not_linearIndependent_pair_of_commute_of_flat_left a b hc
  · exact H.not_linearIndependent_pair_of_commute_of_flat_right a b hc

end

/-- If `M` and `N` are linearly disjoint, if one of `M` and `N` is flat,
if any two elements of `↥(M ⊓ N)` are commutative, then the rank of `↥(M ⊓ N)` is at most one. -/
/-
**Submodule.LinearDisjoint.rank_inf_le_one_of_commute_of_flat** 是 Mathlib 中的一个定理
，位于命名空间 `Submodule.LinearDisjoint`。
形式化陈述：rank_inf_le_one_of_commute_of_flat (hf : Module.Flat R M ∨ Module.Flat R N
) (hc : forall (m n : ↥(M ⊓ N)), Commute m.1 n.1) : Module.rank R ↥(M ⊓ N) <= 1
参数：hf : Module.Flat R M ∨ Module.Flat R N；hc : forall (m n : ↥(M ⊓ N)), Commute 
m.1 n.1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rank_subsingleton`：rank_subsingleton [Subsingleton R] : Module.rank R M 
= 1
· 使用定理 `rank_le`：rank_le {n : Nat} (H : forall s : Finset M, (LinearIndependent 
R fun i : s => (i : M)) -> s.card <= n) : Module.rank R M <= n
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Nontrivial.exists_pair_ne`：∀ {α : Type u_3} [self : Nontrivial α], ∃ x y
, x ≠ y
· 使用定理 `Fintype.one_lt_card_iff_nontrivial`：one_lt_card_iff_nontrivial : 1 < car
d α ↔ Nontrivial α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Submodule.LinearDisjoint.not_linearIndependent_pair_of_commute_of_flat`：
not_linearIndependent_pair_of_commute_of_flat (hf : Module.Flat R M ∨ Module.Fla
t R N) (a b : ↥(M ⊓ N)) (hc : Commute a.1 b.1) : ¬LinearInde…
· 使用定理 `LinearIndependent.comp`：LinearIndependent.comp (h : LinearIndependent R 
v) (f : ι' -> ι) (hf : Injective f) : LinearIndependent R (v ∘ f)
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)

--- 原说明 ---
If `M` and `N` are linearly disjoint, if one of `M` and `N` is flat,
if any two elements of `↥(M ⊓ N)` are commutative, then the rank of `↥(M ⊓ N)` i
s at most one.
-/
theorem rank_inf_le_one_of_commute_of_flat (hf : Module.Flat R M ∨ Module.Flat R N)
    (hc : ∀ (m n : ↥(M ⊓ N)), Commute m.1 n.1) : Module.rank R ↥(M ⊓ N) ≤ 1 := by
  nontriviality R
  refine _root_.rank_le fun s h ↦ ?_
  by_contra hs
  rw [not_le, ← Fintype.card_coe, Fintype.one_lt_card_iff_nontrivial] at hs
  obtain ⟨a, b, hab⟩ := hs.exists_pair_ne
  refine H.not_linearIndependent_pair_of_commute_of_flat hf a.1 b.1 (hc a.1 b.1) ?_
  have := h.comp ![a, b] fun i j hij ↦ by
    fin_cases i <;> fin_cases j
    · rfl
    · simp [hab] at hij
    · simp [hab.symm] at hij
    · rfl
  convert! this
  ext i
  fin_cases i <;> simp

/-- If `M` and `N` are linearly disjoint, if `M` is flat,
if any two elements of `↥(M ⊓ N)` are commutative, then the rank of `↥(M ⊓ N)` is at most one. -/
/-
**Submodule.LinearDisjoint.rank_inf_le_one_of_commute_of_flat_left** 是 Mathlib 中
的一个定理，位于命名空间 `Submodule.LinearDisjoint`。
形式化陈述：rank_inf_le_one_of_commute_of_flat_left [Module.Flat R M] (hc : forall (m 
n : ↥(M ⊓ N)), Commute m.1 n.1) : Module.rank R ↥(M ⊓ N) <= 1
参数：hc : forall (m n : ↥(M ⊓ N)), Commute m.1 n.1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.LinearDisjoint.rank_inf_le_one_of_commute_of_flat`：rank_inf_le
_one_of_commute_of_flat (hf : Module.Flat R M ∨ Module.Flat R N) (hc : forall (m
 n : ↥(M ⊓ N)), Commute m.1 n.1) : Module.rank R …

--- 原说明 ---
If `M` and `N` are linearly disjoint, if `M` is flat,
if any two elements of `↥(M ⊓ N)` are commutative, then the rank of `↥(M ⊓ N)` i
s at most one.
-/
theorem rank_inf_le_one_of_commute_of_flat_left [Module.Flat R M]
    (hc : ∀ (m n : ↥(M ⊓ N)), Commute m.1 n.1) : Module.rank R ↥(M ⊓ N) ≤ 1 :=
  H.rank_inf_le_one_of_commute_of_flat (Or.inl ‹_›) hc

/-- If `M` and `N` are linearly disjoint, if `N` is flat,
if any two elements of `↥(M ⊓ N)` are commutative, then the rank of `↥(M ⊓ N)` is at most one. -/
/-
**Submodule.LinearDisjoint.rank_inf_le_one_of_commute_of_flat_right** 是 Mathlib 
中的一个定理，位于命名空间 `Submodule.LinearDisjoint`。
形式化陈述：rank_inf_le_one_of_commute_of_flat_right [Module.Flat R N] (hc : forall (m
 n : ↥(M ⊓ N)), Commute m.1 n.1) : Module.rank R ↥(M ⊓ N) <= 1
参数：hc : forall (m n : ↥(M ⊓ N)), Commute m.1 n.1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.LinearDisjoint.rank_inf_le_one_of_commute_of_flat`：rank_inf_le
_one_of_commute_of_flat (hf : Module.Flat R M ∨ Module.Flat R N) (hc : forall (m
 n : ↥(M ⊓ N)), Commute m.1 n.1) : Module.rank R …

--- 原说明 ---
If `M` and `N` are linearly disjoint, if `N` is flat,
if any two elements of `↥(M ⊓ N)` are commutative, then the rank of `↥(M ⊓ N)` i
s at most one.
-/
theorem rank_inf_le_one_of_commute_of_flat_right [Module.Flat R N]
    (hc : ∀ (m n : ↥(M ⊓ N)), Commute m.1 n.1) : Module.rank R ↥(M ⊓ N) ≤ 1 :=
  H.rank_inf_le_one_of_commute_of_flat (Or.inr ‹_›) hc

end

/-- If `M` and itself are linearly disjoint, if `M` is flat,
if any two elements of `M` are commutative, then the rank of `M` is at most one. -/
/-
**Submodule.LinearDisjoint.rank_le_one_of_commute_of_flat_of_self** 是 Mathlib 中的
一个定理，位于命名空间 `Submodule.LinearDisjoint`。
形式化陈述：rank_le_one_of_commute_of_flat_of_self (H : M.LinearDisjoint M) [Module.Fl
at R M] (hc : forall (m n : M), Commute m.1 n.1) : Module.rank R M <= 1
参数：H : M.LinearDisjoint M；hc : forall (m n : M), Commute m.1 n.1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Submodule.LinearDisjoint.rank_inf_le_one_of_commute_of_flat_left`：rank_i
nf_le_one_of_commute_of_flat_left [Module.Flat R M] (hc : forall (m n : ↥(M ⊓ N)
), Commute m.1 n.1) : Module.rank R ↥(M ⊓ N) <= 1

--- 原说明 ---
If `M` and itself are linearly disjoint, if `M` is flat,
if any two elements of `M` are commutative, then the rank of `M` is at most one.
-/
theorem rank_le_one_of_commute_of_flat_of_self (H : M.LinearDisjoint M) [Module.Flat R M]
    (hc : ∀ (m n : M), Commute m.1 n.1) : Module.rank R M ≤ 1 := by
  rw [← inf_of_le_left (le_refl M)] at hc ⊢
  exact H.rank_inf_le_one_of_commute_of_flat_left hc

end not_linearIndependent_pair

end LinearDisjoint

end Ring

section CommRing

namespace LinearDisjoint

variable [CommRing R] [CommRing S] [Algebra R S]

variable (M N : Submodule R S)

section not_linearIndependent_pair

variable {M N}

section
variable (H : M.LinearDisjoint N)
include H

section

variable [Nontrivial R]

/-- The `Submodule.LinearDisjoint.not_linearIndependent_pair_of_commute_of_flat_left`
for commutative rings. -/
/-
**Submodule.LinearDisjoint.not_linearIndependent_pair_of_flat_left** 是 Mathlib 中
的一个定理，位于命名空间 `Submodule.LinearDisjoint`。
形式化陈述：not_linearIndependent_pair_of_flat_left [Module.Flat R M] (a b : ↥(M ⊓ N))
 : ¬LinearIndependent R ![a, b]
参数：a b : ↥(M ⊓ N)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.LinearDisjoint.not_linearIndependent_pair_of_commute_of_flat_l
eft`：not_linearIndependent_pair_of_commute_of_flat_left [Module.Flat R M] (a b :
 ↥(M ⊓ N)) (hc : Commute a.1 b.1) : ¬LinearIndependent R ![a, b]
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a

--- 原说明 ---
The `Submodule.LinearDisjoint.not_linearIndependent_pair_of_commute_of_flat_left
`
for commutative rings.
-/
theorem not_linearIndependent_pair_of_flat_left [Module.Flat R M]
    (a b : ↥(M ⊓ N)) : ¬LinearIndependent R ![a, b] :=
  H.not_linearIndependent_pair_of_commute_of_flat_left a b (mul_comm _ _)

/-- The `Submodule.LinearDisjoint.not_linearIndependent_pair_of_commute_of_flat_right`
for commutative rings. -/
/-
**Submodule.LinearDisjoint.not_linearIndependent_pair_of_flat_right** 是 Mathlib 
中的一个定理，位于命名空间 `Submodule.LinearDisjoint`。
形式化陈述：not_linearIndependent_pair_of_flat_right [Module.Flat R N] (a b : ↥(M ⊓ N)
) : ¬LinearIndependent R ![a, b]
参数：a b : ↥(M ⊓ N)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.LinearDisjoint.not_linearIndependent_pair_of_commute_of_flat_r
ight`：not_linearIndependent_pair_of_commute_of_flat_right [Module.Flat R N] (a b
 : ↥(M ⊓ N)) (hc : Commute a.1 b.1) : ¬LinearIndependent R ![a, b]
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a

--- 原说明 ---
The `Submodule.LinearDisjoint.not_linearIndependent_pair_of_commute_of_flat_righ
t`
for commutative rings.
-/
theorem not_linearIndependent_pair_of_flat_right [Module.Flat R N]
    (a b : ↥(M ⊓ N)) : ¬LinearIndependent R ![a, b] :=
  H.not_linearIndependent_pair_of_commute_of_flat_right a b (mul_comm _ _)

/-- The `Submodule.LinearDisjoint.not_linearIndependent_pair_of_commute_of_flat`
for commutative rings. -/
/-
**Submodule.LinearDisjoint.not_linearIndependent_pair_of_flat** 是 Mathlib 中的一个定理
，位于命名空间 `Submodule.LinearDisjoint`。
形式化陈述：not_linearIndependent_pair_of_flat (hf : Module.Flat R M ∨ Module.Flat R N
) (a b : ↥(M ⊓ N)) : ¬LinearIndependent R ![a, b]
参数：hf : Module.Flat R M ∨ Module.Flat R N；a b : ↥(M ⊓ N)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.LinearDisjoint.not_linearIndependent_pair_of_commute_of_flat`：
not_linearIndependent_pair_of_commute_of_flat (hf : Module.Flat R M ∨ Module.Fla
t R N) (a b : ↥(M ⊓ N)) (hc : Commute a.1 b.1) : ¬LinearInde…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a

--- 原说明 ---
The `Submodule.LinearDisjoint.not_linearIndependent_pair_of_commute_of_flat`
for commutative rings.
-/
theorem not_linearIndependent_pair_of_flat (hf : Module.Flat R M ∨ Module.Flat R N)
    (a b : ↥(M ⊓ N)) : ¬LinearIndependent R ![a, b] :=
  H.not_linearIndependent_pair_of_commute_of_flat hf a b (mul_comm _ _)

end

/-- The `Submodule.LinearDisjoint.rank_inf_le_one_of_commute_of_flat`
for commutative rings. -/
/-
**Submodule.LinearDisjoint.rank_inf_le_one_of_flat** 是 Mathlib 中的一个定理，位于命名空间 `Su
bmodule.LinearDisjoint`。
形式化陈述：rank_inf_le_one_of_flat (hf : Module.Flat R M ∨ Module.Flat R N) : Module.
rank R ↥(M ⊓ N) <= 1
参数：hf : Module.Flat R M ∨ Module.Flat R N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.LinearDisjoint.rank_inf_le_one_of_commute_of_flat`：rank_inf_le
_one_of_commute_of_flat (hf : Module.Flat R M ∨ Module.Flat R N) (hc : forall (m
 n : ↥(M ⊓ N)), Commute m.1 n.1) : Module.rank R …
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a

--- 原说明 ---
The `Submodule.LinearDisjoint.rank_inf_le_one_of_commute_of_flat`
for commutative rings.
-/
theorem rank_inf_le_one_of_flat (hf : Module.Flat R M ∨ Module.Flat R N) :
    Module.rank R ↥(M ⊓ N) ≤ 1 :=
  H.rank_inf_le_one_of_commute_of_flat hf fun _ _ ↦ mul_comm _ _

/-- The `Submodule.LinearDisjoint.rank_inf_le_one_of_commute_of_flat_left`
for commutative rings. -/
/-
**Submodule.LinearDisjoint.rank_inf_le_one_of_flat_left** 是 Mathlib 中的一个定理，位于命名空
间 `Submodule.LinearDisjoint`。
形式化陈述：rank_inf_le_one_of_flat_left [Module.Flat R M] : Module.rank R ↥(M ⊓ N) <=
 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.LinearDisjoint.rank_inf_le_one_of_commute_of_flat_left`：rank_i
nf_le_one_of_commute_of_flat_left [Module.Flat R M] (hc : forall (m n : ↥(M ⊓ N)
), Commute m.1 n.1) : Module.rank R ↥(M ⊓ N) <= 1
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a

--- 原说明 ---
The `Submodule.LinearDisjoint.rank_inf_le_one_of_commute_of_flat_left`
for commutative rings.
-/
theorem rank_inf_le_one_of_flat_left [Module.Flat R M] : Module.rank R ↥(M ⊓ N) ≤ 1 :=
  H.rank_inf_le_one_of_commute_of_flat_left fun _ _ ↦ mul_comm _ _

/-- The `Submodule.LinearDisjoint.rank_inf_le_one_of_commute_of_flat_right`
for commutative rings. -/
/-
**Submodule.LinearDisjoint.rank_inf_le_one_of_flat_right** 是 Mathlib 中的一个定理，位于命名
空间 `Submodule.LinearDisjoint`。
形式化陈述：rank_inf_le_one_of_flat_right [Module.Flat R N] : Module.rank R ↥(M ⊓ N) <
= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.LinearDisjoint.rank_inf_le_one_of_commute_of_flat_right`：rank_
inf_le_one_of_commute_of_flat_right [Module.Flat R N] (hc : forall (m n : ↥(M ⊓ 
N)), Commute m.1 n.1) : Module.rank R ↥(M ⊓ N) <= 1
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a

--- 原说明 ---
The `Submodule.LinearDisjoint.rank_inf_le_one_of_commute_of_flat_right`
for commutative rings.
-/
theorem rank_inf_le_one_of_flat_right [Module.Flat R N] : Module.rank R ↥(M ⊓ N) ≤ 1 :=
  H.rank_inf_le_one_of_commute_of_flat_right fun _ _ ↦ mul_comm _ _

end

/-- The `Submodule.LinearDisjoint.rank_le_one_of_commute_of_flat_of_self`
for commutative rings. -/
/-
**Submodule.LinearDisjoint.rank_le_one_of_flat_of_self** 是 Mathlib 中的一个定理，位于命名空间
 `Submodule.LinearDisjoint`。
形式化陈述：rank_le_one_of_flat_of_self (H : M.LinearDisjoint M) [Module.Flat R M] : M
odule.rank R M <= 1
参数：H : M.LinearDisjoint M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.LinearDisjoint.rank_le_one_of_commute_of_flat_of_self`：rank_le
_one_of_commute_of_flat_of_self (H : M.LinearDisjoint M) [Module.Flat R M] (hc :
 forall (m n : M), Commute m.1 n.1) : Module.rank R M…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a

--- 原说明 ---
The `Submodule.LinearDisjoint.rank_le_one_of_commute_of_flat_of_self`
for commutative rings.
-/
theorem rank_le_one_of_flat_of_self (H : M.LinearDisjoint M) [Module.Flat R M] :
    Module.rank R M ≤ 1 :=
  H.rank_le_one_of_commute_of_flat_of_self fun _ _ ↦ mul_comm _ _

end not_linearIndependent_pair

end LinearDisjoint

end CommRing

end Submodule

