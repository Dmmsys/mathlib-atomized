/-
Copyright (c) 2024 Mitchell Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Lee, Junyan Xu
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.RingTheory.Flat.Tensor

/-! # The equational criterion for flatness

Let $M$ be a module over a commutative ring $R$. Let us say that a relation
$\sum_{i \in \iota} f_i x_i = 0$ in $M$ is *trivial* (`Module.IsTrivialRelation`) if there exist a
finite index type $\kappa$ = `Fin k`, elements $(y_j)_{j \in \kappa}$ of $M$,
and elements $(a_{ij})_{i \in \iota, j \in \kappa}$ of $R$ such that for all $i$,
$$x_i = \sum_j a_{ij} y_j$$
and for all $j$,
$$\sum_i f_i a_{ij} = 0.$$

The *equational criterion for flatness* [Stacks 00HK](https://stacks.math.columbia.edu/tag/00HK)
(`Module.Flat.iff_forall_isTrivialRelation`) states that $M$ is flat if and only if every relation
in $M$ is trivial.

The equational criterion for flatness can be stated in the following form
(`Module.Flat.iff_forall_exists_factorization`). Let $M$ be an $R$-module. Then the following two
conditions are equivalent:
* $M$ is flat.
* For finite free modules $R^l$, all elements $f \in R^l$, and all linear maps
  $x \colon R^l \to M$ such that $x(f) = 0$, there exist a finite free module $R^k$ and
  linear maps $a \colon R^l \to R^k$ and $y \colon R^k \to M$ such
  that $x = y \circ a$ and $a(f) = 0$.

Of course, the module $R^l$ in this statement can be replaced by an arbitrary free module
(`Module.Flat.exists_factorization_of_apply_eq_zero_of_free`).

We also have the following strengthening of the equational criterion for flatness
(`Module.Flat.exists_factorization_of_comp_eq_zero_of_free`): Let $M$ be a
flat module. Let $K$ and $N$ be finite $R$-modules with $N$ free, and let $f \colon K \to N$ and
$x \colon N \to M$ be linear maps such that $x \circ f = 0$. Then there exist a finite free module
$R^k$ and linear maps $a \colon N \to R^k$ and $y \colon R^k \to M$ such
that $x = y \circ a$ and $a \circ f = 0$. We recover the usual equational criterion for flatness if
$K = R$ and $N = R^l$. This is used in the proof of Lazard's theorem.

We conclude that every linear map from a finitely presented module to a flat module factors
through a finite free module (`Module.Flat.exists_factorization_of_finitePresentation`), and
every finitely presented flat module is projective (`Module.Flat.projective_of_finitePresentation`).

## References

* [Stacks: Flat modules and flat ring maps](https://stacks.math.columbia.edu/tag/00H9)
* [Stacks: Characterizing flatness](https://stacks.math.columbia.edu/tag/058C)

-/

public section

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

open LinearMap TensorProduct Finsupp

namespace Module

variable {ι : Type*} [Fintype ι] (f : ι → R) (x : ι → M)

/-- The proposition that the relation $\sum_i f_i x_i = 0$ in $M$ is trivial.
That is, there exist a finite index type $\kappa$ = `Fin k`, elements
$(y_j)_{j \in \kappa}$ of $M$, and elements $(a_{ij})_{i \in \iota, j \in \kappa}$ of $R$
such that for all $i$,
$$x_i = \sum_j a_{ij} y_j$$
and for all $j$,
$$\sum_i f_i a_{ij} = 0.$$
By `Module.sum_smul_eq_zero_of_isTrivialRelation`, this condition implies $\sum_i f_i x_i = 0$. -/
/-
**Module.IsTrivialRelation** 是 Mathlib 中的一个缩写定义，位于命名空间 `Module`。
形式化陈述：IsTrivialRelation : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The proposition that the relation $\sum_i f_i x_i = 0$ in $M$ is trivial.
That is, there exist a finite index type $\kappa$ = `Fin k`, elements
$(y_j)_{j \in \kappa}$ of $M$, and elements $(a_{ij})_{i \in \iota, j \in \kappa
}$ of $R$
such that for all $i$,
$$x_i = \sum_j a_{ij} y_j$$
and for all $j$,
$$\sum_i f_i a_{ij} = 0.$$
By `Module.sum_smul_eq_zero_of_isTrivialRelation`, this condition implies $\sum_
i f_i x_i = 0$.
-/
abbrev IsTrivialRelation : Prop :=
  ∃ (k : ℕ) (a : ι → Fin k → R) (y : Fin k → M),
    (∀ i, x i = ∑ j, a i j • y j) ∧ ∀ j, ∑ i, f i * a i j = 0

variable {f x}

/-- `Module.IsTrivialRelation` is equivalent to the predicate `TensorProduct.VanishesTrivially`
defined in `Mathlib/LinearAlgebra/TensorProduct/Vanishing.lean`. -/
/-
**Module.isTrivialRelation_iff_vanishesTrivially** 是 Mathlib 中的一个定理，位于命名空间 `Modu
le`。
形式化陈述：isTrivialRelation_iff_vanishesTrivially : IsTrivialRelation f x ↔ Vanishes
Trivially R f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
`Module.IsTrivialRelation` is equivalent to the predicate `TensorProduct.Vanishe
sTrivially`
defined in `Mathlib/LinearAlgebra/TensorProduct/Vanishing.lean`.
-/
theorem isTrivialRelation_iff_vanishesTrivially :
    IsTrivialRelation f x ↔ VanishesTrivially R f x := by
  simp only [IsTrivialRelation, VanishesTrivially, smul_eq_mul, mul_comm]
/-
**Module._root_.Equiv.isTrivialRelation_comp** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Equiv.isTrivialRelation_comp {κ} [Fintype κ] (e : κ ≃ ι) :
    IsTrivialRelation (f ∘ e) (x ∘ e) ↔ IsTrivialRelation f x := by
  simp_rw [isTrivialRelation_iff_vanishesTrivially, e.vanishesTrivially_comp]

/-- If the relation given by $(f_i)_{i \in \iota}$ and $(x_i)_{i \in \iota}$ is trivial, then
$\sum_i f_i x_i$ is actually equal to $0$. -/
/-
**Module.sum_smul_eq_zero_of_isTrivialRelation** 是 Mathlib 中的一个定理，位于命名空间 `Module
`。
形式化陈述：sum_smul_eq_zero_of_isTrivialRelation (h : IsTrivialRelation f x) : ∑ i, f
 i • x i = 0
参数：h : IsTrivialRelation f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `TensorProduct.sum_tmul_eq_zero_of_vanishesTrivially`：sum_tmul_eq_zero_of
_vanishesTrivially (hmn : VanishesTrivially R m n) : ∑ i, m i otimesₜ n i = (0 :
 M otimes[R] N)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.isTrivialRelation_iff_vanishesTrivially`：isTrivialRelation_iff_va
nishesTrivially : IsTrivialRelation f x ↔ VanishesTrivially R f x

--- 原说明 ---
If the relation given by $(f_i)_{i \in \iota}$ and $(x_i)_{i \in \iota}$ is triv
ial, then
$\sum_i f_i x_i$ is actually equal to $0$.
-/
theorem sum_smul_eq_zero_of_isTrivialRelation (h : IsTrivialRelation f x) :
    ∑ i, f i • x i = 0 := by
  simpa using
    congr_arg (TensorProduct.lid R M) <|
      sum_tmul_eq_zero_of_vanishesTrivially R (isTrivialRelation_iff_vanishesTrivially.mp h)

end Module

namespace Module.Flat

variable (R M) in
/-- **Equational criterion for flatness**, combined form.

Let $M$ be a module over a commutative ring $R$. The following are equivalent:
* $M$ is flat.
* For all ideals $I \subseteq R$, the map $I \otimes M \to M$ is injective.
* Every $\sum_i f_i \otimes x_i$ that vanishes in $R \otimes M$ vanishes trivially.
* Every relation $\sum_i f_i x_i = 0$ in $M$ is trivial.
* For all finite free modules $R^l$, all elements $f \in R^l$, and all linear maps
  $x \colon R^l \to M$ such that $x(f) = 0$, there exist a finite free module $R^k$ and
  linear maps $a \colon R^l \to R^k$ and $y \colon R^k \to M$ such
  that $x = y \circ a$ and $a(f) = 0$.
-/
@[stacks 00HK, stacks 058D "(1) ↔ (2)"]
/-
**Module.Flat.tfae_equational_criterion** 是 Mathlib 中的一个定理，位于命名空间 `Module.Flat`。
形式化陈述：tfae_equational_criterion : List.TFAE [ Flat R M, forall I : Ideal R, Func
tion.Injective (rTensor M I.subtype), forall {l : Nat} {f : Fin l -> R} {x : Fin
 l -> M}, ∑ i, f i otimesₜ x i = (0 : R otimes[R] M) -> VanishesTrivially R f x,
 forall {l : Nat} {f : Fin l -> R} {x : Fin l -> M}, ∑ i, f i • x i = 0 -> IsTri
vialRelation f x, forall {l : Nat} {f : Fin l ->₀ R} {x : (Fin l ->₀ R) ->ₗ[R] M
}, x f = 0 -> exists (k : Nat) (a : (Fin l ->₀ R) ->ₗ[R] (Fin k ->₀ R)) (y : (Fi
n k ->₀ R) ->ₗ[R] M), x = 
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Flat.iff_rTensor_injective'`：iff_rTensor_injective' : Flat R M ↔ 
forall I : Ideal R, Function.Injective (rTensor M I.subtype)
· 使用定理 `TensorProduct.forall_vanishesTrivially_iff_forall_rTensor_injective`：for
all_vanishesTrivially_iff_forall_rTensor_injective : (forall {l : Nat} {m : Fin 
l -> M} {n : Fin l -> N}, ∑ i, m i otimesₜ n i = (0 : M o…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
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
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.smul_single`：smul_single [Zero M] [SMulZeroClass R M] (c : R) (a
 : α) (b : M) : c • Finsupp.single a b = Finsupp.single a (c • b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finsupp.univ_sum_single`：univ_sum_single [Fintype α] [AddCommMonoid M] (
f : α ->₀ M) : ∑ a : α, single a (f a) = f
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂
（共 51 条，此处仅展示前 30 条）

--- 原说明 ---
**Equational criterion for flatness**, combined form.

Let $M$ be a module over a commutative ring $R$. The following are equivalent:
* $M$ is flat.
* For all ideals $I \subseteq R$, the map $I \otimes M \to M$ is injective.
* Every $\sum_i f_i \otimes x_i$ that vanishes in $R \otimes M$ vanishes trivial
ly.
* Every relation $\sum_i f_i x_i = 0$ in $M$ is trivial.
* For all finite free modules $R^l$, all elements $f \in R^l$, and all linear ma
ps
  $x \colon R^l \to M$ such that $x(f) = 0$, there exist a finite free module $R
^k$ and
  linear maps $a \colon R^l \to R^k$ and $y \colon R^k \to M$ such
  that $x = y \circ a$ and $a(f) = 0$.
-/
theorem tfae_equational_criterion : List.TFAE [
    Flat R M,
    ∀ I : Ideal R, Function.Injective (rTensor M I.subtype),
    ∀ {l : ℕ} {f : Fin l → R} {x : Fin l → M}, ∑ i, f i ⊗ₜ x i = (0 : R ⊗[R] M) →
      VanishesTrivially R f x,
    ∀ {l : ℕ} {f : Fin l → R} {x : Fin l → M}, ∑ i, f i • x i = 0 → IsTrivialRelation f x,
    ∀ {l : ℕ} {f : Fin l →₀ R} {x : (Fin l →₀ R) →ₗ[R] M}, x f = 0 →
      ∃ (k : ℕ) (a : (Fin l →₀ R) →ₗ[R] (Fin k →₀ R)) (y : (Fin k →₀ R) →ₗ[R] M),
        x = y ∘ₗ a ∧ a f = 0] := by
  tfae_have 1 ↔ 2 := iff_rTensor_injective'
  tfae_have 3 ↔ 2 := forall_vanishesTrivially_iff_forall_rTensor_injective R
  tfae_have 3 ↔ 4 := by
    simp [(TensorProduct.lid R M).injective.eq_iff.symm, isTrivialRelation_iff_vanishesTrivially]
  tfae_have 4 → 5
  | h₄, l, f, x, hfx => by
    let f' : Fin l → R := f
    let x' : Fin l → M := fun i ↦ x (single i 1)
    have := calc
      ∑ i, f' i • x' i
      _ = ∑ i, f i • x (single i 1) := rfl
      _ = x (∑ i, f i • Finsupp.single i 1) := by simp_rw [map_sum, map_smul]
      _ = x f := by simp_rw [smul_single, smul_eq_mul, mul_one, univ_sum_single]
      _ = 0 := hfx
    obtain ⟨k, a', y', ⟨ha'y', ha'⟩⟩ := h₄ this
    use k
    use Finsupp.linearCombination R (fun i ↦ equivFunOnFinite.symm (a' i))
    use Finsupp.linearCombination R y'
    constructor
    · apply Finsupp.basisSingleOne.ext
      intro i
      simpa [linearCombination_apply, sum_fintype, Finsupp.single_apply] using ha'y' i
    · ext j
      simp only [linearCombination_apply, zero_smul, implies_true, sum_fintype, finsetSum_apply]
      exact ha' j
  tfae_have 5 → 4
  | h₅, l, f, x, hfx => by
    let f' : Fin l →₀ R := equivFunOnFinite.symm f
    let x' : (Fin l →₀ R) →ₗ[R] M := Finsupp.linearCombination R x
    have : x' f' = 0 := by simpa [x', f', linearCombination_apply, sum_fintype] using hfx
    obtain ⟨k, a', y', ha'y', ha'⟩ := h₅ this
    refine ⟨k, fun i ↦ a' (single i 1), fun j ↦ y' (single j 1), fun i ↦ ?_, fun j ↦ ?_⟩
    · simpa [x', ← map_smul, ← map_sum, smul_single] using
        LinearMap.congr_fun ha'y' (Finsupp.single i 1)
    · simp_rw [← smul_eq_mul, ← Finsupp.smul_apply, ← map_smul, ← finsetSum_apply, ← map_sum,
        smul_single, smul_eq_mul, mul_one,
        ← (fun _ ↦ equivFunOnFinite_symm_apply_apply _ _ : ∀ x, f' x = f x), univ_sum_single]
      simpa using DFunLike.congr_fun ha' j
  tfae_finish

/-- **Equational criterion for flatness**:
a module $M$ is flat if and only if every relation $\sum_i f_i x_i = 0$ in $M$ is trivial. -/
@[stacks 00HK]
/-
**Module.Flat.iff_forall_isTrivialRelation** 是 Mathlib 中的一个定理，位于命名空间 `Module.Fla
t`。
形式化陈述：iff_forall_isTrivialRelation : Flat R M ↔ forall {l : Nat} {f : Fin l -> R
} {x : Fin l -> M}, ∑ i, f i • x i = 0 -> IsTrivialRelation f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `Module.Flat.tfae_equational_criterion`：tfae_equational_criterion : List.
TFAE [ Flat R M, forall I : Ideal R, Function.Injective (rTensor M I.subtype), f
orall {l : Nat} {f : Fin l …

--- 原说明 ---
**Equational criterion for flatness**:
a module $M$ is flat if and only if every relation $\sum_i f_i x_i = 0$ in $M$ i
s trivial.
-/
theorem iff_forall_isTrivialRelation : Flat R M ↔ ∀ {l : ℕ} {f : Fin l → R} {x : Fin l → M},
    ∑ i, f i • x i = 0 → IsTrivialRelation f x :=
  (tfae_equational_criterion R M).out 0 3

/-- **Equational criterion for flatness**, forward direction.

If $M$ is flat, then every relation $\sum_i f_i x_i = 0$ in $M$ is trivial. -/
@[stacks 00HK]
/-
**Module.Flat.isTrivialRelation_of_sum_smul_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `M
odule.Flat`。
形式化陈述：isTrivialRelation_of_sum_smul_eq_zero [Flat R M] {ι : Type*} [Fintype ι] {
f : ι -> R} {x : ι -> M} (h : ∑ i, f i • x i = 0) : IsTrivialRelation f x
参数：h : ∑ i, f i • x i = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.isTrivialRelation_comp`：∀ {R : Type u_1} {M : Type u_2} [inst : Co
mmRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {ι : Type u_3
} [inst_3 : Fintyp…
· 使用定理 `Module.Flat.iff_forall_isTrivialRelation`：iff_forall_isTrivialRelation :
 Flat R M ↔ forall {l : Nat} {f : Fin l -> R} {x : Fin l -> M}, ∑ i, f i • x i =
 0 -> IsTrivialRelation f x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.sum_comp`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : F
intype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι ≃ κ) (g : κ →
 M),…

--- 原说明 ---
**Equational criterion for flatness**, forward direction.

If $M$ is flat, then every relation $\sum_i f_i x_i = 0$ in $M$ is trivial.
-/
theorem isTrivialRelation_of_sum_smul_eq_zero [Flat R M] {ι : Type*} [Fintype ι] {f : ι → R}
    {x : ι → M} (h : ∑ i, f i • x i = 0) : IsTrivialRelation f x :=
  (Fintype.equivFin ι).symm.isTrivialRelation_comp.mp <| iff_forall_isTrivialRelation.mp ‹_› <| by
    simpa only [← (Fintype.equivFin ι).symm.sum_comp] using! h

/-- **Equational criterion for flatness**, backward direction.

If every relation $\sum_i f_i x_i = 0$ in $M$ is trivial, then $M$ is flat. -/
@[stacks 00HK]
/-
**Module.Flat.of_forall_isTrivialRelation** 是 Mathlib 中的一个定理，位于命名空间 `Module.Flat
`。
形式化陈述：of_forall_isTrivialRelation (hfx : forall {l : Nat} {f : Fin l -> R} {x : 
Fin l -> M}, ∑ i, f i • x i = 0 -> IsTrivialRelation f x) : Flat R M
参数：hfx : forall {l : Nat} {f : Fin l -> R} {x : Fin l -> M}, ∑ i, f i • x i = 0 
-> IsTrivialRelation f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.Flat.iff_forall_isTrivialRelation`：iff_forall_isTrivialRelation :
 Flat R M ↔ forall {l : Nat} {f : Fin l -> R} {x : Fin l -> M}, ∑ i, f i • x i =
 0 -> IsTrivialRelation f x

--- 原说明 ---
**Equational criterion for flatness**, backward direction.

If every relation $\sum_i f_i x_i = 0$ in $M$ is trivial, then $M$ is flat.
-/
theorem of_forall_isTrivialRelation (hfx : ∀ {l : ℕ} {f : Fin l → R} {x : Fin l → M},
    ∑ i, f i • x i = 0 → IsTrivialRelation f x) : Flat R M :=
  iff_forall_isTrivialRelation.mpr hfx

/-- **Equational criterion for flatness**, alternate form.

A module $M$ is flat if and only if for all finite free modules $R^l$,
all $f \in R^l$, and all linear maps $x \colon R^l \to M$ such that $x(f) = 0$, there
exist a finite free module $R^k$ and linear maps $a \colon R^l \to R^k$ and
$y \colon R^k \to M$ such that $x = y \circ a$ and $a(f) = 0$. -/
@[stacks 058D "(1) ↔ (2)"]
/-
**Module.Flat.iff_forall_exists_factorization** 是 Mathlib 中的一个定理，位于命名空间 `Module.
Flat`。
形式化陈述：iff_forall_exists_factorization : Flat R M ↔ forall {l : Nat} {f : Fin l -
>₀ R} {x : (Fin l ->₀ R) ->ₗ[R] M}, x f = 0 -> exists (k : Nat) (a : (Fin l ->₀ 
R) ->ₗ[R] (Fin k ->₀ R)) (y : (Fin k ->₀ R) ->ₗ[R] M), x = y ∘ₗ a ∧ a f = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `Module.Flat.tfae_equational_criterion`：tfae_equational_criterion : List.
TFAE [ Flat R M, forall I : Ideal R, Function.Injective (rTensor M I.subtype), f
orall {l : Nat} {f : Fin l …

--- 原说明 ---
**Equational criterion for flatness**, alternate form.

A module $M$ is flat if and only if for all finite free modules $R^l$,
all $f \in R^l$, and all linear maps $x \colon R^l \to M$ such that $x(f) = 0$, 
there
exist a finite free module $R^k$ and linear maps $a \colon R^l \to R^k$ and
$y \colon R^k \to M$ such that $x = y \circ a$ and $a(f) = 0$.
-/
theorem iff_forall_exists_factorization : Flat R M ↔
    ∀ {l : ℕ} {f : Fin l →₀ R} {x : (Fin l →₀ R) →ₗ[R] M}, x f = 0 →
      ∃ (k : ℕ) (a : (Fin l →₀ R) →ₗ[R] (Fin k →₀ R)) (y : (Fin k →₀ R) →ₗ[R] M),
        x = y ∘ₗ a ∧ a f = 0 := (tfae_equational_criterion R M).out 0 4

/-- **Equational criterion for flatness**, backward direction, alternate form.

Let $M$ be a module over a commutative ring $R$. Suppose that for all finite free modules $R^l$,
all $f \in R^l$, and all linear maps $x \colon R^l \to M$ such that $x(f) = 0$, there
exist a finite free module $R^k$ and linear maps $a \colon R^l \to R^k$ and
$y \colon R^k \to M$ such that $x = y \circ a$ and $a(f) = 0$. Then $M$ is flat. -/
@[stacks 058D "(2) → (1)"]
/-
**Module.Flat.of_forall_exists_factorization** 是 Mathlib 中的一个定理，位于命名空间 `Module.F
lat`。
形式化陈述：of_forall_exists_factorization (h : forall {l : Nat} {f : Fin l ->₀ R} {x 
: (Fin l ->₀ R) ->ₗ[R] M}, x f = 0 -> exists (k : Nat) (a : (Fin l ->₀ R) ->ₗ[R]
 (Fin k ->₀ R)) (y : (Fin k ->₀ R) ->ₗ[R] M), x = y ∘ₗ a ∧ a f = 0) : Flat R M
参数：h : forall {l : Nat} {f : Fin l ->₀ R} {x : (Fin l ->₀ R) ->ₗ[R] M}, x f = 0 
-> exists (k : Nat) (a : (Fin l ->₀ R) ->ₗ[R] (Fin k ->₀ R)) (y : (Fin k ->₀ R) 
->ₗ[R] M), x = y ∘ₗ a ∧ a f = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.Flat.iff_forall_exists_factorization`：iff_forall_exists_factoriza
tion : Flat R M ↔ forall {l : Nat} {f : Fin l ->₀ R} {x : (Fin l ->₀ R) ->ₗ[R] M
}, x f = 0 -> exists (k : Nat) (a…

--- 原说明 ---
**Equational criterion for flatness**, backward direction, alternate form.

Let $M$ be a module over a commutative ring $R$. Suppose that for all finite fre
e modules $R^l$,
all $f \in R^l$, and all linear maps $x \colon R^l \to M$ such that $x(f) = 0$, 
there
exist a finite free module $R^k$ and linear maps $a \colon R^l \to R^k$ and
$y \colon R^k \to M$ such that $x = y \circ a$ and $a(f) = 0$. Then $M$ is flat.
-/
theorem of_forall_exists_factorization
    (h : ∀ {l : ℕ} {f : Fin l →₀ R} {x : (Fin l →₀ R) →ₗ[R] M}, x f = 0 →
      ∃ (k : ℕ) (a : (Fin l →₀ R) →ₗ[R] (Fin k →₀ R)) (y : (Fin k →₀ R) →ₗ[R] M),
      x = y ∘ₗ a ∧ a f = 0) : Flat R M := iff_forall_exists_factorization.mpr h

/-- **Equational criterion for flatness**, forward direction, second alternate form.

Let $M$ be a flat module over a commutative ring $R$. Let $N$ be a finite free module over $R$,
let $f \in N$, and let $x \colon N \to M$ be a linear map such that $x(f) = 0$. Then there exist a
finite free module $R^k$ and linear maps $a \colon N \to R^k$ and
$y \colon R^k \to M$ such that $x = y \circ a$ and $a(f) = 0$. -/
@[stacks 058D "(1) → (2)"]
/-
**Module.Flat.exists_factorization_of_apply_eq_zero_of_free** 是 Mathlib 中的一个定理，位
于命名空间 `Module.Flat`。
形式化陈述：exists_factorization_of_apply_eq_zero_of_free [Flat R M] {N : Type*} [AddC
ommGroup N] [Module R N] [Free R N] [Module.Finite R N] {f : N} {x : N ->ₗ[R] M}
 (h : x f = 0) : exists (k : Nat) (a : N ->ₗ[R] (Fin k ->₀ R)) (y : (Fin k ->₀ R
) ->ₗ[R] M), x = y ∘ₗ a ∧ a f = 0
参数：h : x f = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.Flat.iff_forall_exists_factorization`：iff_forall_exists_factoriza
tion : Flat R M ↔ forall {l : Nat} {f : Fin l ->₀ R} {x : (Fin l ->₀ R) ->ₗ[R] M
}, x f = 0 -> exists (k : Nat) (a…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.comp_assoc`：comp_assoc {R₄ M₄ : Type*} [Semiring R₄] [AddCommM
onoid M₄] [Module R₄ M₄] {σ₃₄ : R₃ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₁₄ : R₁ ->+* R₄
} [RingHom…
· 使用定理 `LinearEquiv.eq_comp_toLinearMap_symm`：eq_comp_toLinearMap_symm (f : M₂ -
>ₛₗ[σ₂₃] M₃) (g : M₁ ->ₛₗ[σ₁₃] M₃) : f = g.comp e₁₂.symm.toLinearMap ↔ f.comp e₁
₂.toLinearMap = g

--- 原说明 ---
**Equational criterion for flatness**, forward direction, second alternate form.

Let $M$ be a flat module over a commutative ring $R$. Let $N$ be a finite free m
odule over $R$,
let $f \in N$, and let $x \colon N \to M$ be a linear map such that $x(f) = 0$. 
Then there exist a
finite free module $R^k$ and linear maps $a \colon N \to R^k$ and
$y \colon R^k \to M$ such that $x = y \circ a$ and $a(f) = 0$.
-/
theorem exists_factorization_of_apply_eq_zero_of_free [Flat R M] {N : Type*} [AddCommGroup N]
    [Module R N] [Free R N] [Module.Finite R N] {f : N} {x : N →ₗ[R] M} (h : x f = 0) :
    ∃ (k : ℕ) (a : N →ₗ[R] (Fin k →₀ R)) (y : (Fin k →₀ R) →ₗ[R] M), x = y ∘ₗ a ∧ a f = 0 :=
  have e := ((Module.Free.chooseBasis R N).reindex (Fintype.equivFin _)).repr.symm
  have ⟨k, a, y, hya, haf⟩ := iff_forall_exists_factorization.mp ‹Flat R M›
    (f := e.symm f) (x := x ∘ₗ e) (by simpa using h)
  ⟨k, a ∘ₗ e.symm, y, by rwa [← comp_assoc, LinearEquiv.eq_comp_toLinearMap_symm], haf⟩
/-
**Module.Flat.exists_factorization_of_comp_eq_zero_of_free_aux** 是 Mathlib 中的一个定
理，位于命名空间 `Module.Flat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem exists_factorization_of_comp_eq_zero_of_free_aux [Flat R M] {K : Type*} {n : ℕ}
    [AddCommGroup K] [Module R K] [Module.Finite R K] {f : K →ₗ[R] Fin n →₀ R}
    {x : (Fin n →₀ R) →ₗ[R] M} (h : x ∘ₗ f = 0) :
    ∃ (k : ℕ) (a : (Fin n →₀ R) →ₗ[R] (Fin k →₀ R)) (y : (Fin k →₀ R) →ₗ[R] M),
      x = y ∘ₗ a ∧ a ∘ₗ f = 0 := by
  have (K' : Submodule R K) (hK' : K'.FG) : ∃ (k : ℕ) (a : (Fin n →₀ R) →ₗ[R] (Fin k →₀ R))
      (y : (Fin k →₀ R) →ₗ[R] M), x = y ∘ₗ a ∧ K' ≤ LinearMap.ker (a ∘ₗ f) := by
    induction K', hK' using Submodule.fg_induction generalizing n with
    | singleton k =>
      have : x (f k) = 0 := by simpa using LinearMap.congr_fun h k
      simpa using exists_factorization_of_apply_eq_zero_of_free this
    | sup K₁ K₂ _ _ ih₁ ih₂ =>
      obtain ⟨k₁, a₁, y₁, rfl, ha₁⟩ := ih₁ h
      have : y₁ ∘ₗ (a₁ ∘ₗ f) = 0 := by rw [← comp_assoc, h]
      obtain ⟨k₂, a₂, y₂, rfl, ha₂⟩ := ih₂ this
      use k₂, a₂ ∘ₗ a₁, y₂
      simp_rw [comp_assoc]
      exact ⟨trivial, sup_le (ha₁.trans (ker_le_ker_comp _ _)) ha₂⟩
  convert! this ⊤ Finite.fg_top
  simp only [top_le_iff, ker_eq_top]

/-- Let $M$ be a flat module. Let $K$ and $N$ be finite $R$-modules with $N$
free, and let $f \colon K \to N$ and $x \colon N \to M$ be linear maps such that
$x \circ f = 0$. Then there exist a finite free module $R^k$ and linear maps
$a \colon N \to R^k$ and $y \colon R^k \to M$ such that $x = y \circ a$ and
$a \circ f = 0$. -/
@[stacks 058D "(1) → (4)"]
/-
**Module.Flat.exists_factorization_of_comp_eq_zero_of_free** 是 Mathlib 中的一个定理，位于
命名空间 `Module.Flat`。
形式化陈述：exists_factorization_of_comp_eq_zero_of_free [Flat R M] {K N : Type*} [Add
CommGroup K] [Module R K] [Module.Finite R K] [AddCommGroup N] [Module R N] [Fre
e R N] [Module.Finite R N] {f : K ->ₗ[R] N} {x : N ->ₗ[R] M} (h : x ∘ₗ f = 0) : 
exists (k : Nat) (a : N ->ₗ[R] (Fin k ->₀ R)) (y : (Fin k ->₀ R) ->ₗ[R] M), x = 
y ∘ₗ a ∧ a ∘ₗ f = 0
参数：h : x ∘ₗ f = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.RingTheory.Flat.EquationalCriterion.0.Module.Flat.exist
s_factorization_of_comp_eq_zero_of_free_aux`：∀ {R : Type u_1} {M : Type u_2} [in
st : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [Modul
e.Flat R M] {K : Type u_3…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用引理 `LinearEquiv.comp_symm_assoc`：comp_symm_assoc (f : M₃ ->ₛₗ[σ₃₂] M₂) [Ring
HomCompTriple σ₃₁ σ₁₂ σ₃₂] : e₁₂.toLinearMap ∘ₛₗ e₁₂.symm.toLinearMap ∘ₛₗ f = f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.comp_assoc`：comp_assoc {R₄ M₄ : Type*} [Semiring R₄] [AddCommM
onoid M₄] [Module R₄ M₄] {σ₃₄ : R₃ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₁₄ : R₁ ->+* R₄
} [RingHom…
· 使用定理 `LinearEquiv.eq_comp_toLinearMap_symm`：eq_comp_toLinearMap_symm (f : M₂ -
>ₛₗ[σ₂₃] M₃) (g : M₁ ->ₛₗ[σ₁₃] M₃) : f = g.comp e₁₂.symm.toLinearMap ↔ f.comp e₁
₂.toLinearMap = g

--- 原说明 ---
Let $M$ be a flat module. Let $K$ and $N$ be finite $R$-modules with $N$
free, and let $f \colon K \to N$ and $x \colon N \to M$ be linear maps such that
$x \circ f = 0$. Then there exist a finite free module $R^k$ and linear maps
$a \colon N \to R^k$ and $y \colon R^k \to M$ such that $x = y \circ a$ and
$a \circ f = 0$.
-/
theorem exists_factorization_of_comp_eq_zero_of_free [Flat R M] {K N : Type*} [AddCommGroup K]
    [Module R K] [Module.Finite R K] [AddCommGroup N] [Module R N] [Free R N] [Module.Finite R N]
    {f : K →ₗ[R] N} {x : N →ₗ[R] M} (h : x ∘ₗ f = 0) :
    ∃ (k : ℕ) (a : N →ₗ[R] (Fin k →₀ R)) (y : (Fin k →₀ R) →ₗ[R] M),
      x = y ∘ₗ a ∧ a ∘ₗ f = 0 :=
  have e := ((Module.Free.chooseBasis R N).reindex (Fintype.equivFin _)).repr.symm
  have ⟨k, a, y, hya, haf⟩ := exists_factorization_of_comp_eq_zero_of_free_aux
    (f := e.symm ∘ₗ f) (x := x ∘ₗ e.toLinearMap) (by ext; simpa [comp_assoc] using congr($h _))
  ⟨k, a ∘ₗ e.symm, y, by rwa [← comp_assoc, LinearEquiv.eq_comp_toLinearMap_symm], by
    rwa [comp_assoc]⟩

/-- Every homomorphism from a finitely presented module to a flat module factors through a finite
free module. -/
@[stacks 058E "only if"]
/-
**Module.Flat.exists_factorization_of_finitePresentation** 是 Mathlib 中的一个定理，位于命名
空间 `Module.Flat`。
形式化陈述：exists_factorization_of_finitePresentation [Flat R M] {P : Type*} [AddComm
Group P] [Module R P] [FinitePresentation R P] (h₁ : P ->ₗ[R] M) : exists (k : N
at) (h₂ : P ->ₗ[R] (Fin k ->₀ R)) (h₃ : (Fin k ->₀ R) ->ₗ[R] M), h₁ = h₃ ∘ₗ h₂
参数：h₁ : P ->ₗ[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.FinitePresentation.exists_fin`：Module.FinitePresentation.exists_f
in [fp : Module.FinitePresentation R M] : exists (n : Nat) (K : Submodule R (Fin
 n -> R)) (_ : M ≃ₗ[R] (Fi…
· 使用定理 `Module.Finite.of_fg`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N : Submodule R M}, 
N.FG → Mo…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `Function.Exact.linearMap_comp_eq_zero`：∀ {R : Type u_1} {M : Type u_2} {
N : Type u_4} {P : Type u_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [i
nst_2 : AddCommMonoid N] [i…
· 使用引理 `LinearMap.exact_subtype_mkQ`：exact_subtype_mkQ (Q : Submodule R N) : Exa
ct (Submodule.subtype Q) (Submodule.mkQ Q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.comp_zero`：comp_zero (g : M₂ ->ₛₗ[σ₂₃] M₃) : (g.comp (0 : M ->
ₛₗ[σ₁₂] M₂) : M ->ₛₗ[σ₁₃] M₃) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Module.Flat.exists_factorization_of_comp_eq_zero_of_free`：exists_factori
zation_of_comp_eq_zero_of_free [Flat R M] {K N : Type*} [AddCommGroup K] [Module
 R K] [Module.Finite R K] [AddCommGroup N] [Mo…
· 使用定理 `Module.Free.function`：∀ (ι : Type u_1) (R : Type u_2) (M : Type u_3) [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [Fini
te ι] [Mod…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.range_le_ker_iff`：range_le_ker_iff {f : M ->ₛₗ[τ₁₂] M₂} {g : M
₂ ->ₛₗ[τ₂₃] M₃} : range f <= ker g ↔ (g.comp f : M ->ₛₗ[τ₁₃] M₃) = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.cancel_right`：cancel_right (hg : Surjective g) : f.comp g = f'
.comp g ↔ f = f'
· 使用定理 `LinearEquiv.surjective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {
M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMono
id M] [inst_…
· 使用定理 `Submodule.mkQ_surjective`：mkQ_surjective : Function.Surjective p.mkQ
· 使用定理 `LinearEquiv.symm_trans_self`：symm_trans_self (f : M₁ ≃ₛₗ[σ₁₂] M₂) : f.sy
mm.trans f = LinearEquiv.refl R₂ M₂
· 使用定理 `Submodule.liftQ_mkQ`：liftQ_mkQ (f : M ->ₛₗ[τ₁₂] M₂) (h) : (p.liftQ f h).
comp p.mkQ = f

--- 原说明 ---
Every homomorphism from a finitely presented module to a flat module factors thr
ough a finite
free module.
-/
theorem exists_factorization_of_finitePresentation [Flat R M] {P : Type*} [AddCommGroup P]
    [Module R P] [FinitePresentation R P] (h₁ : P →ₗ[R] M) :
    ∃ (k : ℕ) (h₂ : P →ₗ[R] (Fin k →₀ R)) (h₃ : (Fin k →₀ R) →ₗ[R] M), h₁ = h₃ ∘ₗ h₂ := by
  have ⟨_, K, ϕ, hK⟩ := FinitePresentation.exists_fin R P
  have : Module.Finite R K := .of_fg hK
  have : (h₁ ∘ₗ ϕ.symm ∘ₗ K.mkQ) ∘ₗ K.subtype = 0 := by
    simp_rw [comp_assoc, (LinearMap.exact_subtype_mkQ K).linearMap_comp_eq_zero, comp_zero]
  obtain ⟨k, a, y, hay, ha⟩ := exists_factorization_of_comp_eq_zero_of_free this
  use k, (K.liftQ a (by rwa [← range_le_ker_iff, Submodule.range_subtype] at ha)) ∘ₗ ϕ, y
  apply (cancel_right ϕ.symm.surjective).mp
  apply (cancel_right K.mkQ_surjective).mp
  simpa [comp_assoc]

@[deprecated (since := "2026-05-23")]
alias exists_factorization_of_isFinitelyPresented := exists_factorization_of_finitePresentation

@[stacks 00NX "(1) → (2)"]
/-
**Module.Flat.projective_of_finitePresentation** 是 Mathlib 中的一个定理，位于命名空间 `Module
.Flat`。
形式化陈述：projective_of_finitePresentation [Flat R M] [FinitePresentation R M] : Pro
jective R M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Flat.exists_factorization_of_finitePresentation`：exists_factoriza
tion_of_finitePresentation [Flat R M] {P : Type*} [AddCommGroup P] [Module R P] 
[FinitePresentation R P] (h₁ : P ->ₗ[R] M) :…
· 使用定理 `Module.Projective.of_split`：∀ {R : Type u_1} [inst : Semiring R] {P : Ty
pe u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   {M : Type u_3}
 [inst_3 : AddCo…
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用定理 `Module.Free.finsupp`：∀ (R : Type u_1) (M : Type u_2) (ι : Type u_3) [ins
t : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [Modul
e.Free R …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem projective_of_finitePresentation [Flat R M] [FinitePresentation R M] : Projective R M :=
  have ⟨_, f, g, eq⟩ := exists_factorization_of_finitePresentation (.id (R := R) (M := M))
  .of_split f g eq.symm

end Module.Flat

