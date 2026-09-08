/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.Matrix
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Lie.Weights.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Matrix
public import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix

/-!
# Geck's construction of a Lie algebra associated to a root system

This file contains an implementation of Geck's construction of a semisimple Lie algebra from a
reduced crystallographic root system. It follows [Geck](Geck2017) quite closely.

## Main definitions:
* `RootPairing.GeckConstruction.lieAlgebra`: the Geck construction of the Lie algebra associated to
  a root system with distinguished base.
* `RootPairing.GeckConstruction.cartanSubalgebra`: a distinguished subalgebra corresponding to a
  Cartan subalgebra of the Geck construction.
* `RootPairing.GeckConstruction.cartanSubalgebra_le_lieAlgebra`: the distinguished subalgebra is
  contained in the Geck construction.

## Alternative approaches

There are at least three ways to construct a Lie algebra from a root system:
1. As a quotient of a free Lie algebra, using the Serre relations
2. Directly defining the Lie bracket on $H ⊕ K^∣Φ|$
3. The Geck construction

We comment on these as follows:
1. This construction takes just a matrix as input. It yields a semisimple Lie algebra iff the
   matrix is a Cartan matrix but it is quite a lot of work to prove this. On the other hand, it also
   allows construction of Kac-Moody Lie algebras. It has been implemented as `Matrix.ToLieAlgebra`
   but as of May 2025, almost nothing has been proved about it in Mathlib.
2. This construction takes a root system with base as input, together with sufficient additional
   data to determine a collection of extraspecial pairs of roots. The additional data for the
   extraspecial pairs is required to pin down certain signs when defining the Lie bracket. (These
   signs can be interpreted as a set-theoretic splitting of Tits's extension of the Weyl group by
   an elementary 2-group of order $2^l$ where $l$ is the rank.)
3. This construction takes a root system with base as input and is implemented here.

There seems to be no known construction of a Lie algebra from a root system without first choosing
a base: https://mathoverflow.net/questions/495434/

-/

@[expose] public section

noncomputable section

open Function Set Submodule
open scoped Matrix

attribute [local simp] Matrix.mul_apply Matrix.one_apply Matrix.diagonal_apply

namespace RootPairing.GeckConstruction

variable {ι R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] {b : P.Base}

/-- Part of an `sl₂` triple used in Geck's construction of a Lie algebra from a root system. -/
/-
**RootPairing.GeckConstruction.h** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing.GeckCons
truction`。
形式化陈述：h (i : b.support) : Matrix (b.support oplus ι) (b.support oplus ι) R
参数：i : b.support。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Part of an `sl₂` triple used in Geck's construction of a Lie algebra from a root
 system.
-/
def h (i : b.support) :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
  open scoped Classical in
  .fromBlocks 0 0 0 (.diagonal (P.pairingIn ℤ · i))
/-
**RootPairing.GeckConstruction.h_def** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Geck
Construction`。
形式化陈述：h_def [DecidableEq ι] (i : b.support) : h i = .fromBlocks 0 0 0 (.diagonal
 (P.pairingIn Int · i))
参数：i : b.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma h_def [DecidableEq ι] (i : b.support) :
    h i = .fromBlocks 0 0 0 (.diagonal (P.pairingIn ℤ · i)) := by
  ext (j | j) (k | k) <;> simp [h, Matrix.diagonal_apply]
/-
**RootPairing.GeckConstruction.h_eq_diagonal** 是 Mathlib 中的一个引理，位于命名空间 `RootPair
ing.GeckConstruction`。
形式化陈述：h_eq_diagonal [DecidableEq ι] (i : b.support) : h i = .diagonal (Sum.elim 
0 (P.pairingIn Int · i))
参数：i : b.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `Sum.inl.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : α), (Sum.inl val
 = Sum.inl val_1) = (val = val_1)
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.diagonal_apply_ne`：diagonal_apply_ne [Zero α] (d : n -> α) {i j :
 n} (h : i != j) : (diagonal d) i j = 0
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
-/
lemma h_eq_diagonal [DecidableEq ι] (i : b.support) :
    h i = .diagonal (Sum.elim 0 (P.pairingIn ℤ · i)) := by
  ext (j | j) (k | k) <;> simp [h, Matrix.diagonal_apply]

variable (b) in
/-
**RootPairing.GeckConstruction.linearIndependent_h** 是 Mathlib 中的一个引理，位于命名空间 `Ro
otPairing.GeckConstruction`。
形式化陈述：linearIndependent_h [Finite ι] [CharZero R] [IsDomain R] [P.IsRootSystem] 
: LinearIndependent R (h (b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用引理 `RootPairing.GeckConstruction.h_def`：h_def [DecidableEq ι] (i : b.support
) : h i = .fromBlocks 0 0 0 (.diagonal (P.pairingIn Int · i))
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.diagLinearMap_apply`：∀ (n : Type u_3) (R : Type u_7) (α : Type u_
11) [inst : Semiring R] [inst_1 : AddCommMonoid α]   [inst_2 : _root_.Module R α
] (a : Matrix n …
· 使用定理 `Matrix.diagAddMonoidHom_apply`：∀ (n : Type u_3) (α : Type u_11) [inst : 
AddZeroClass α] (A : Matrix n n α) (i : n),   (Matrix.diagAddMonoidHom n α) A i 
= A.diag i
· 使用定理 `Sum.elimZeroLeft_apply`：∀ {ι : Type u_6} {κ : Type u_7} {R : Type u_8} [
inst : Semiring R] (g : ι → R) (a : κ ⊕ ι),   Sum.elimZeroLeft g a = Sum.elim 0 
g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
· 使用定理 `LinearIndependent.of_comp`：LinearIndependent.of_comp (f : M ->ₗ[R] M') (
hfv : LinearIndependent R (f ∘ v)) : LinearIndependent R v
· 使用定理 `LinearMap.linearIndependent_iff_of_injOn`：∀ {ι : Type u'} {R : Type u_2}
 {M : Type u_4} {M' : Type u_5} {v : ι → M} [inst : Semiring R] [inst_1 : AddCom
mMonoid M]   [inst_2 : AddComm…
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Sum.elim_injective'`：elim_injective' {γ : Sort*} {f : α -> γ} : Injectiv
e (Sum.elim f : (β -> γ) -> (α oplus β -> γ))
· 使用定理 `linearIndependent_algebraMap_comp_iff`：∀ {ι : Type u_1} {ι' : Type u_2} 
[Finite ι'] {R : Type u_3} {S : Type u_4} [inst : CommRing R] [inst_1 : CommRing
 S]   [inst_2 : Algebra R S…
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用定理 `Matrix.linearIndependent_rows_of_det_ne_zero`：linearIndependent_rows_of_
det_ne_zero [IsDomain R] {A : Matrix m m R} (hA : A.det != 0) : LinearIndependen
t R (fun i => A i)
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `Matrix.det_transpose`：det_transpose (M : Matrix n n R) : Mᵀ.det = M.det
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.nondegenerate_iff_det_ne_zero`：nondegenerate_iff_det_ne_zero [Dec
idableEq n] : Nondegenerate M ↔ M.det != 0
· 使用引理 `RootPairing.Base.cartanMatrix_nondegenerate`：cartanMatrix_nondegenerate 
{P : RootPairing ι R M N} [P.IsRootSystem] [P.IsCrystallographic] (b : P.Base) :
 b.cartanMatrix.Nondegenerate
· 使用引理 `LinearIndependent.of_linearIndependent_subset`：LinearIndependent.of_line
arIndependent_subset (s : Set ι') {v : ι -> ι' -> R} (hv : LinearIndependent R f
un (i : ι) (j : s) => v i j) : Line…
-/
lemma linearIndependent_h [Finite ι] [CharZero R] [IsDomain R] [P.IsRootSystem] :
    LinearIndependent R (h (b := b)) := by
  classical
  have : Matrix.diagLinearMap (b.support ⊕ ι) R R ∘ h =
      Sum.elimZeroLeft ∘ fun i : b.support ↦ algebraMap ℤ R ∘ (P.pairingIn ℤ · i) := by
    ext; rw [comp_apply, h_def]; aesop
  apply LinearIndependent.of_comp (Matrix.diagLinearMap _ _ _)
  rw [this, LinearMap.linearIndependent_iff_of_injOn _ Sum.elim_injective'.injOn,
    linearIndependent_algebraMap_comp_iff]
  suffices LinearIndependent ℤ (fun i j : b.support ↦ P.pairingIn ℤ j i) from
    this.of_linearIndependent_subset b.support
  apply b.cartanMatrix.transpose.linearIndependent_rows_of_det_ne_zero
  rw [Matrix.det_transpose, ← Matrix.nondegenerate_iff_det_ne_zero]
  exact b.cartanMatrix_nondegenerate
/-
**RootPairing.GeckConstruction.span_range_h_le_range_diagonal** 是 Mathlib 中的一个引理
，位于命名空间 `RootPairing.GeckConstruction`。
形式化陈述：span_range_h_le_range_diagonal [DecidableEq ι] : span R (range h) <= Linea
rMap.range (Matrix.diagonalLinearMap (b.support oplus ι) R R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用引理 `RootPairing.GeckConstruction.h_eq_diagonal`：h_eq_diagonal [DecidableEq ι
] (i : b.support) : h i = .diagonal (Sum.elim 0 (P.pairingIn Int · i))
· 使用定理 `LinearMap.mem_range_self`：mem_range_self [RingHomSurjective τ₁₂] (f : M 
->ₛₗ[τ₁₂] M₂) (x : M) : f x in range f
-/
lemma span_range_h_le_range_diagonal [DecidableEq ι] :
    span R (range h) ≤ LinearMap.range (Matrix.diagonalLinearMap (b.support ⊕ ι) R R) := by
  rw [span_le]
  rintro - ⟨i, rfl⟩
  rw [h_eq_diagonal]
  exact LinearMap.mem_range_self _ _

open Matrix in
/-
**RootPairing.GeckConstruction.diagonal_elim_mem_span_h_iff** 是 Mathlib 中的一个定理，位
于命名空间 `RootPairing.GeckConstruction`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] {P : RootPairing ι R M N}   [inst_5 : P.
IsCrystallographic] {b : P.Base} [inst_6 : DecidableEq ι] {d : ι → R},   Matrix.
diagonal (Sum.elim 0 d) ∈ Submodule.span R (Set.range RootPairing.GeckConstructi
on.h) ↔     d ∈ Submodule.span R (Set.range fun i j => ↑(P.pairingIn ℤ j ↑i))
参数：Sum.elim 0 d；Set.range RootPairing.GeckConstruction.h；Set.range fun i j => ↑(
P.pairingIn ℤ j ↑i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.diagonalLinearMap_apply`：∀ (n : Type u_3) (R : Type u_7) (α : Typ
e u_11) [inst : DecidableEq n] [inst_1 : Semiring R] [inst_2 : AddCommMonoid α] 
  [inst_3 : _root_.M…
· 使用定理 `Matrix.diagonalAddMonoidHom_apply`：∀ (n : Type u_3) (α : Type u_11) [ins
t : DecidableEq n] [inst_1 : AddZeroClass α] (d : n → α),   (Matrix.diagonalAddM
onoidHom n α) d = Matri…
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `Sum.inl.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : α), (Sum.inl val
 = Sum.inl val_1) = (val = val_1)
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.diagonal_apply_ne`：diagonal_apply_ne [Zero α] (d : n -> α) {i j :
 n} (h : i != j) : (diagonal d) i j = 0
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用引理 `RootPairing.GeckConstruction.h_def`：h_def [DecidableEq ι] (i : b.support
) : h i = .fromBlocks 0 0 0 (.diagonal (P.pairingIn Int · i))
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Submodule.span_image`：span_image [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂
] M₂) : span R₂ (f '' s) = map f (span R s)
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 32 条，此处仅展示前 30 条）
-/
@[simp] lemma diagonal_elim_mem_span_h_iff [DecidableEq ι] {d : ι → R} :
    diagonal (Sum.elim 0 d) ∈ span R (range <| h (b := b)) ↔
      d ∈ span R (range <| fun (i : b.support) j ↦ (P.pairingIn ℤ j i : R)) := by
  let g : Matrix ι ι R →ₗ[R] Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
    { toFun := .fromBlocks 0 0 0
      map_add' x y := by ext (i | i) (j | j) <;> simp
      map_smul' t x := by ext (i | i) (j | j) <;> simp }
  have h₀ : Injective (g ∘ diagonalLinearMap ι R R) := fun _ _ hd ↦ funext <| by simpa [g] using hd
  have h₁ {d : ι → R} : diagonal (Sum.elim 0 d) = g (diagonalLinearMap ι R R d) := by
    ext (i | i) (j | j) <;> simp [g]
  have h₂ : range h = g '' (diagonalLinearMap ι R R ''
    (range <| fun (i : b.support) j ↦ (P.pairingIn ℤ j i : R))) := by ext; simp [g, h_def]
  simp_rw [h₁, h₂, span_image, ← map_comp, ← comp_apply (f := g), mem_map, LinearMap.coe_comp,
    h₀.eq_iff, exists_eq_right]
/-
**RootPairing.GeckConstruction.apply_sum_inl_eq_zero_of_mem_span_h** 是 Mathlib 中
的一个引理，位于命名空间 `RootPairing.GeckConstruction`。
形式化陈述：apply_sum_inl_eq_zero_of_mem_span_h (i : b.support) (j : b.support oplus ι
) {x : Matrix (b.support oplus ι) (b.support oplus ι) R} (hx : x in span R (rang
e h)) : x j (Sum.inl i) = 0
参数：i : b.support；j : b.support oplus ι；b.support oplus ι；b.support oplus ι；hx : 
x in span R (range h)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
lemma apply_sum_inl_eq_zero_of_mem_span_h
    (i : b.support) (j : b.support ⊕ ι) {x : Matrix (b.support ⊕ ι) (b.support ⊕ ι) R}
    (hx : x ∈ span R (range h)) :
    x j (Sum.inl i) = 0 := by
  induction hx using span_induction with
  | mem x h => obtain ⟨i, rfl⟩ := h; cases j <;> simp [h]
  | zero => simp
  | add u v _ _ hu hv => simp [hu, hv]
  | smul t u _ hu => simp [hu]
/-
**RootPairing.GeckConstruction.lie_h_h** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Ge
ckConstruction`。
形式化陈述：lie_h_h [Fintype ι] (i j : b.support) : ⁅h i, h j⁆ = 0
参数：i j : b.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `RootPairing.GeckConstruction.h_eq_diagonal`：h_eq_diagonal [DecidableEq ι
] (i : b.support) : h i = .diagonal (Sum.elim 0 (P.pairingIn Int · i))
· 使用定理 `Matrix.commute_diagonal`：commute_diagonal {α : Type*} [NonUnitalNonAssoc
CommSemiring α] [Fintype n] [DecidableEq n] (d₁ d₂ : n -> α) : Commute (diagonal
 d₁) (diagona…
-/
lemma lie_h_h [Fintype ι] (i j : b.support) :
    ⁅h i, h j⁆ = 0 := by
  classical
  simpa only [h_eq_diagonal, ← commute_iff_lie_eq] using Matrix.commute_diagonal _ _

variable [Finite ι] [IsDomain R] [CharZero R]

/-- Part of an `sl₂` triple used in Geck's construction of a Lie algebra from a root system. -/
/-
**RootPairing.GeckConstruction.e** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing.GeckCons
truction`。
形式化陈述：e (i : b.support) : Matrix (b.support oplus ι) (b.support oplus ι) R
参数：i : b.support。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Part of an `sl₂` triple used in Geck's construction of a Lie algebra from a root
 system.
-/
def e (i : b.support) :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
  open scoped Classical in
  letI := P.indexNeg
  .fromBlocks 0
    (.of fun i' j ↦ if i' = i ∧ j = -i then 1 else 0)
    (.of fun i' j ↦ if i' = i then ↑|b.cartanMatrix i j| else 0)
    (.of fun i' j ↦ if P.root i' = P.root i + P.root j then P.chainBotCoeff i j + 1 else 0)

/-- Part of an `sl₂` triple used in Geck's construction of a Lie algebra from a root system. -/
/-
**RootPairing.GeckConstruction.f** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing.GeckCons
truction`。
形式化陈述：f (i : b.support) : Matrix (b.support oplus ι) (b.support oplus ι) R
参数：i : b.support。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Part of an `sl₂` triple used in Geck's construction of a Lie algebra from a root
 system.
-/
def f (i : b.support) :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
  open scoped Classical in
  letI := P.indexNeg
  .fromBlocks 0
    (.of fun i' j ↦ if i' = i ∧ j = i then 1 else 0)
    (.of fun i' j ↦ if i' = -i then ↑|b.cartanMatrix i j| else 0)
    (.of fun i' j ↦ if P.root i' = P.root j - P.root i then P.chainTopCoeff i j + 1 else 0)

variable (b)

/-- An involutive matrix which can transfer results between `RootPairing.GeckConstruction.e` and
`RootPairing.GeckConstruction.f`. -/
/-
**RootPairing.GeckConstruction.** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing.GeckConst
ruction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An involutive matrix which can transfer results between `RootPairing.GeckConstru
ction.e` and
`RootPairing.GeckConstruction.f`.
-/
def ω :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
  open scoped Classical in
  letI := P.indexNeg
  .fromBlocks 1 0 0 <| .of fun i j ↦ if i = -j then 1 else 0

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Geck's construction of the Lie algebra associated to a root system with distinguished base.

Note that it is convenient to include `range h` in the Lie span, to make it elementary that it
contains `RootPairing.GeckConstruction.cartanSubalgebra`, and not depend on
`RootPairing.GeckConstruction.lie_e_f_same`. -/
/-
**RootPairing.GeckConstruction.lieAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing
.GeckConstruction`。
形式化陈述：lieAlgebra [Fintype ι] [DecidableEq ι] : LieSubalgebra R (Matrix (b.suppor
t oplus ι) (b.support oplus ι) R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Geck's construction of the Lie algebra associated to a root system with distingu
ished base.

Note that it is convenient to include `range h` in the Lie span, to make it elem
entary that it
contains `RootPairing.GeckConstruction.cartanSubalgebra`, and not depend on
`RootPairing.GeckConstruction.lie_e_f_same`.
-/
def lieAlgebra [Fintype ι] [DecidableEq ι] :
    LieSubalgebra R (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R) :=
  LieSubalgebra.lieSpan R _ (range h ∪ range e ∪ range f)

/-- A distinguished subalgebra corresponding to a Cartan subalgebra of the Geck construction.

See also `RootPairing.GeckConstruction.cartanSubalgebra'`. -/
/-
**RootPairing.GeckConstruction.cartanSubalgebra** 是 Mathlib 中的一个定义，位于命名空间 `RootP
airing.GeckConstruction`。
形式化陈述：cartanSubalgebra [Fintype ι] [DecidableEq ι] : LieSubalgebra R (Matrix (b.
support oplus ι) (b.support oplus ι) R) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A distinguished subalgebra corresponding to a Cartan subalgebra of the Geck cons
truction.

See also `RootPairing.GeckConstruction.cartanSubalgebra'`.
-/
def cartanSubalgebra [Fintype ι] [DecidableEq ι] :
    LieSubalgebra R (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R) where
  __ := Submodule.span R (range h)
  lie_mem' {x y} hx hy := by
    have aux : (∀ u ∈ range (h (b := b)), ∀ v ∈ range (h (b := b)), ⁅u, v⁆ = 0) := by
      rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩; exact lie_h_h i j
    simp only [Submodule.carrier_eq_coe, SetLike.mem_coe, LieSubalgebra.mem_toSubmodule,
      ← LieSubalgebra.coe_lieSpan_eq_span_of_forall_lie_eq_zero (R := R) aux] at hx hy ⊢
    exact LieSubalgebra.lie_mem _ hx hy

/-- A distinguished Cartan subalgebra of the Geck construction. -/
/-
**RootPairing.GeckConstruction.cartanSubalgebra'** 是 Mathlib 中的一个定义，位于命名空间 `Root
Pairing.GeckConstruction`。
形式化陈述：cartanSubalgebra' [Fintype ι] [DecidableEq ι] : LieSubalgebra R (lieAlgebr
a b)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A distinguished Cartan subalgebra of the Geck construction.
-/
def cartanSubalgebra' [Fintype ι] [DecidableEq ι] :
    LieSubalgebra R (lieAlgebra b) :=
  (cartanSubalgebra b).comap (lieAlgebra b).incl

omit [Finite ι] [IsDomain R] [CharZero R] in
/-
**RootPairing.GeckConstruction.cartanSubalgebra_eq_lieSpan** 是 Mathlib 中的一个引理，位于
命名空间 `RootPairing.GeckConstruction`。
形式化陈述：cartanSubalgebra_eq_lieSpan [Fintype ι] [DecidableEq ι] : cartanSubalgebra
 b = LieSubalgebra.lieSpan R _ (range h)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LieSubalgebra.submodule_span_le_lieSpan`：submodule_span_le_lieSpan : Sub
module.span R s <= lieSpan R L s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubalgebra.lieSpan_le`：lieSpan_le {K} : lieSpan R L s <= K ↔ s subset
eq K
· 使用定理 `RootPairing.GeckConstruction.cartanSubalgebra.eq_1`：∀ {ι : Type u_1} {R 
: Type u_2} {M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommG
roup M]   [inst_2 : _root_.Module R M] […
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
-/
lemma cartanSubalgebra_eq_lieSpan [Fintype ι] [DecidableEq ι] :
    cartanSubalgebra b = LieSubalgebra.lieSpan R _ (range h) := by
  refine le_antisymm LieSubalgebra.submodule_span_le_lieSpan ?_
  rw [LieSubalgebra.lieSpan_le, cartanSubalgebra]
  exact Submodule.subset_span

variable {b}

omit [Finite ι] [IsDomain R] [CharZero R] in
/-
**RootPairing.GeckConstruction.h_mem_cartanSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 
`RootPairing.GeckConstruction`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] {P : RootPairing ι R M N}   [inst_5 : P.
IsCrystallographic] {b : P.Base} [inst_6 : Fintype ι] [inst_7 : DecidableEq ι] (
i : ↥b.support),   RootPairing.GeckConstruction.h i ∈ RootPairing.GeckConstructi
on.cartanSubalgebra b
参数：i : ↥b.support。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
@[simp] lemma h_mem_cartanSubalgebra [Fintype ι] [DecidableEq ι] (i : b.support) :
    h i ∈ cartanSubalgebra b :=
  Submodule.subset_span <| mem_range_self i
/-
**RootPairing.GeckConstruction.h_mem_cartanSubalgebra'** 是 Mathlib 中的一个定理，位于命名空间
 `RootPairing.GeckConstruction`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] {P : RootPairing ι R M N}   [inst_5 : P.
IsCrystallographic] {b : P.Base} [inst_6 : Finite ι] [inst_7 : IsDomain R] [inst
_8 : CharZero R]   [inst_9 : Fintype ι] [inst_10 : DecidableEq ι] (i : ↥b.suppor
t)   (hi : RootPairing.GeckConstruction.h i ∈ RootPairing.GeckConstruction.lieAl
gebra b),   ⟨RootPairing.GeckConstruction.h i, hi⟩ ∈ RootPairing.GeckConstructio
n.cartanSubalgebra' b
参数：i : ↥b.support；hi : RootPairing.GeckConstruction.h i ∈ RootPairing.GeckConstr
uction.lieAlgebra b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
@[simp] lemma h_mem_cartanSubalgebra' [Fintype ι] [DecidableEq ι] (i : b.support) (hi) :
    ⟨h i, hi⟩ ∈ cartanSubalgebra' b := by
  simp [cartanSubalgebra']
/-
**RootPairing.GeckConstruction.h_mem_lieAlgebra** 是 Mathlib 中的一个引理，位于命名空间 `RootP
airing.GeckConstruction`。
形式化陈述：h_mem_lieAlgebra [Fintype ι] [DecidableEq ι] (i : b.support) : h i in lieA
lgebra b
参数：i : b.support。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.subset_lieSpan`：subset_lieSpan : s subseteq lieSpan R L s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
lemma h_mem_lieAlgebra [Fintype ι] [DecidableEq ι] (i : b.support) :
    h i ∈ lieAlgebra b :=
  LieSubalgebra.subset_lieSpan <| by simp
/-
**RootPairing.GeckConstruction.e_mem_lieAlgebra** 是 Mathlib 中的一个引理，位于命名空间 `RootP
airing.GeckConstruction`。
形式化陈述：e_mem_lieAlgebra [Fintype ι] [DecidableEq ι] (i : b.support) : e i in lieA
lgebra b
参数：i : b.support。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.subset_lieSpan`：subset_lieSpan : s subseteq lieSpan R L s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
lemma e_mem_lieAlgebra [Fintype ι] [DecidableEq ι] (i : b.support) :
    e i ∈ lieAlgebra b :=
  LieSubalgebra.subset_lieSpan <| by simp
/-
**RootPairing.GeckConstruction.f_mem_lieAlgebra** 是 Mathlib 中的一个引理，位于命名空间 `RootP
airing.GeckConstruction`。
形式化陈述：f_mem_lieAlgebra [Fintype ι] [DecidableEq ι] (i : b.support) : f i in lieA
lgebra b
参数：i : b.support。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.subset_lieSpan`：subset_lieSpan : s subseteq lieSpan R L s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
lemma f_mem_lieAlgebra [Fintype ι] [DecidableEq ι] (i : b.support) :
    f i ∈ lieAlgebra b :=
  LieSubalgebra.subset_lieSpan <| by simp

/-- The element `h i`, as a term of the Cartan subalgebra `cartanSubalgebra' b`. -/
/-
**RootPairing.GeckConstruction.h'** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing.GeckCon
struction`。
形式化陈述：h' [Fintype ι] [DecidableEq ι] (i : b.support) : cartanSubalgebra' b
参数：i : b.support。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.GeckConstruction.h_mem_lieAlgebra`：h_mem_lieAlgebra [Fintype
 ι] [DecidableEq ι] (i : b.support) : h i in lieAlgebra b

--- 原说明 ---
The element `h i`, as a term of the Cartan subalgebra `cartanSubalgebra' b`.
-/
def h' [Fintype ι] [DecidableEq ι] (i : b.support) : cartanSubalgebra' b :=
  ⟨⟨h i, h_mem_lieAlgebra i⟩, h_mem_cartanSubalgebra' i (h_mem_lieAlgebra i)⟩

variable (b) in
@[simp]
/-
**RootPairing.GeckConstruction.span_range_h'_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `R
ootPairing.GeckConstruction`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] {P : RootPairing ι R M N}   [inst_5 : P.
IsCrystallographic] (b : P.Base) [inst_6 : Finite ι] [inst_7 : IsDomain R] [inst
_8 : CharZero R]   [inst_9 : Fintype ι] [inst_10 : DecidableEq ι], Submodule.spa
n R (Set.range RootPairing.GeckConstruction.h') = ⊤
参数：b : P.Base；Set.range RootPairing.GeckConstruction.h'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LieSubalgebra.instIsScalarTowerSubtypeMem`：∀ (R : Type u) (L : Type v) [
inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] {R₁ : Type u_1
}   [inst_3 : Semiring R₁] [ins…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Function.Injective.mem_set_image`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β}, Function.Injective f → ∀ {s : Set α} {a : α}, f a ∈ f '' s ↔ a ∈ s
· 使用定理 `Submodule.injective_subtype`：injective_subtype : Injective p.subtype
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
-/
lemma span_range_h'_eq_top [Fintype ι] [DecidableEq ι] :
    span R (range h') = (⊤ : Submodule R (cartanSubalgebra' b)) := by
  rw [eq_top_iff]
  rintro ⟨⟨x, -⟩, hx : x ∈ span R (range h)⟩ -
  let g : cartanSubalgebra' b →ₗ[R] Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
    (lieAlgebra b).subtype ∘ₗ (cartanSubalgebra' b).subtype
  suffices x ∈ (span R (range h')).map g by
    rwa [← SetLike.mem_coe, ← (injective_subtype _).mem_set_image,
        ← (injective_subtype _).mem_set_image, ← image_comp]
  rwa [map_span, ← range_comp]

omit [Finite ι] [IsDomain R] [CharZero R] [P.IsCrystallographic] in
/-
**RootPairing.GeckConstruction.** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.GeckConst
ruction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ω_mul_ω [DecidableEq ι] [Fintype ι] :
    ω b * ω b = 1 := by
  ext (k | k) (l | l) <;>
  simp [ω, -indexNeg_neg]

omit [Finite ι] [IsDomain R] in
/-
**RootPairing.GeckConstruction.** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.GeckConst
ruction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ω_mul_h [Fintype ι] (i : b.support) :
    ω b * h i = -h i * ω b := by
  classical
  ext (k | k) (l | l)
  · simp [ω, h]
  · simp [ω, h]
  · simp [ω, h]
  · simp only [ω, h, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₂]
    aesop
/-
**RootPairing.GeckConstruction.** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.GeckConst
ruction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ω_mul_e [Fintype ι] (i : b.support) :
    ω b * e i = f i * ω b := by
  let := P.indexNeg
  classical
  ext (k | k) (l | l)
  · simp [ω, e, f]
  · simp only [ω, e, f, mul_ite, mul_zero, Fintype.sum_sum_type, Matrix.mul_apply, Matrix.of_apply,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Finset.sum_ite_eq']
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _) (by simp_all)]
    simp [← ite_and, and_comm, -indexNeg_neg, neg_eq_iff_eq_neg]
  · simp [ω, e, f]
  · simp only [ω, e, f, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.of_apply, mul_ite, ← neg_eq_iff_eq_neg (a := k)]
    rw [Finset.sum_eq_single_of_mem (-k) (Finset.mem_univ _) (by aesop)]
    simp [neg_eq_iff_eq_neg, sub_eq_add_neg]
/-
**RootPairing.GeckConstruction.** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.GeckConst
ruction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ω_mul_f [Fintype ι] (i : b.support) :
    ω b * f i = e i * ω b := by
  classical
  have := congr_arg (· * ω b) (congr_arg (ω b * ·) (ω_mul_e i))
  simp only [← mul_assoc, ω_mul_ω] at this
  simpa [mul_assoc, ω_mul_ω] using this.symm
/-
**RootPairing.GeckConstruction.lie_e_f_mul_** 是 Mathlib 中的一个引理，位于命名空间 `RootPairi
ng.GeckConstruction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lie_e_f_mul_ω [Fintype ι] (i j : b.support) :
    ⁅e i, f j⁆ * ω b = -ω b * ⁅e j, f i⁆ := by
  calc ⁅e i, f j⁆ * ω b = e i * f j * ω b - f j * e i * ω b := by rw [Ring.lie_def, sub_mul]
                      _ = e i * (f j * ω b) - f j * (e i * ω b) := by rw [mul_assoc, mul_assoc]
                      _ = e i * (ω b * e j) - f j * (ω b * f i) := by rw [← ω_mul_e, ← ω_mul_f]
                      _ = (e i * ω b) * e j - (f j * ω b) * f i := by rw [← mul_assoc, ← mul_assoc]
                      _ = (ω b * f i) * e j - (ω b * e j) * f i := by rw [← ω_mul_e, ← ω_mul_f]
                      _ = ω b * (f i * e j) - ω b * (e j * f i) := by rw [mul_assoc, mul_assoc]
                      _ = -ω b * ⁅e j, f i⁆ := ?_
  rw [Ring.lie_def, mul_sub, neg_mul, neg_mul, sub_neg_eq_add]
  abel

variable [DecidableEq ι]

/-- Geck's name for the "left" basis elements of `b.support ⊕ ι`. -/
/-
**RootPairing.GeckConstruction.u** 是 Mathlib 中的一个缩写定义，位于命名空间 `RootPairing.GeckCo
nstruction`。
形式化陈述：u (i : b.support) : b.support oplus ι -> R
参数：i : b.support。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Geck's name for the "left" basis elements of `b.support ⊕ ι`.
-/
abbrev u (i : b.support) : b.support ⊕ ι → R := Pi.single (Sum.inl i) 1

variable (b) in
/-- Geck's name for the "right" basis elements of `b.support ⊕ ι`. -/
/-
**RootPairing.GeckConstruction.v** 是 Mathlib 中的一个缩写定义，位于命名空间 `RootPairing.GeckCo
nstruction`。
形式化陈述：v (i : ι) : b.support oplus ι -> R
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Geck's name for the "right" basis elements of `b.support ⊕ ι`.
-/
abbrev v (i : ι) : b.support ⊕ ι → R := Pi.single (Sum.inr i) 1

variable (b) in
omit [Finite ι] [IsDomain R] [CharZero R] [P.IsCrystallographic] in
/-
**RootPairing.GeckConstruction.apply_inr_eq_zero_of_mem_span_range_u** 是 Mathlib
 中的一个引理，位于命名空间 `RootPairing.GeckConstruction`。
形式化陈述：apply_inr_eq_zero_of_mem_span_range_u (j : ι) {x : b.support oplus ι -> R}
 (hx : x in span R (range u)) : x (Sum.inr j) = 0
参数：j : ι；hx : x in span R (range u)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
lemma apply_inr_eq_zero_of_mem_span_range_u (j : ι) {x : b.support ⊕ ι → R}
    (hx : x ∈ span R (range u)) : x (Sum.inr j) = 0 := by
  induction hx using span_induction with
  | mem x h => obtain ⟨i, rfl⟩ := h; simp [u]
  | zero => simp
  | add u v _ _ hu hv => simp [hu, hv]
  | smul t u _ hu => simp [hu]
/-
**RootPairing.GeckConstruction.lie_e_lie_f_apply** 是 Mathlib 中的一个引理，位于命名空间 `Root
Pairing.GeckConstruction`。
形式化陈述：lie_e_lie_f_apply [Fintype ι] (i j : b.support) : ⁅e i, ⁅f i, u j⁆⁆ = |b.c
artanMatrix i j| • u i
参数：i j : b.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.mulVec_single`：mulVec_single [Fintype n] [DecidableEq n] [NonUnit
alNonAssocSemiring R] (M : Matrix m n R) (j : n) (x : R) : M *ᵥ Pi.single j x = 
MulOpposit…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Fintype.sum_sum_type`：∀ {α₁ : Type u_4} {α₂ : Type u_5} {M : Type u_6} [
inst : Fintype α₁] [inst_1 : Fintype α₂] [inst_2 : AddCommMonoid M]   (f : α₁ ⊕ 
α₂ → M), ∑…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
· 使用定理 `Sum.inl.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : α), (Sum.inl val
 = Sum.inl val_1) = (val = val_1)
· 使用定理 `smul_ite`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a b : α) (c : β),   (c • if p then a else b) = if p the…
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用引理 `RootPairing.root_reflectionPerm`：root_reflectionPerm (j : ι) : P.root (P
.reflectionPerm i j) = (P.reflection i) (P.root j)
（共 41 条，此处仅展示前 30 条）
-/
lemma lie_e_lie_f_apply [Fintype ι] (i j : b.support) :
    ⁅e i, ⁅f i, u j⁆⁆ = |b.cartanMatrix i j| • u i := by
  ext (k | k)
  · simp [e, f, Matrix.mulVec, dotProduct, Pi.single_apply]
  · simp [e, f, Matrix.mulVec, dotProduct, P.ne_zero]

variable [Fintype ι]
/-
**RootPairing.GeckConstruction.** 是 Mathlib 中的一个实例，位于命名空间 `RootPairing.GeckConst
ruction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsLieAbelian (cartanSubalgebra b) := by
  rw [cartanSubalgebra_eq_lieSpan, LieSubalgebra.isLieAbelian_lieSpan_iff]
  rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩
  exact lie_h_h i j
/-
**RootPairing.GeckConstruction.** 是 Mathlib 中的一个实例，位于命名空间 `RootPairing.GeckConst
ruction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsLieAbelian (cartanSubalgebra' b) := by
  refine ⟨fun ⟨⟨x, hx⟩, hx'⟩ ⟨⟨y, hy⟩, hy'⟩ ↦ ?_⟩
  let x' : cartanSubalgebra b := ⟨x, hx'⟩
  let y' : cartanSubalgebra b := ⟨y, hy'⟩
  suffices ⁅x', y'⁆ = 0 by simpa [x', y', Subtype.ext_iff] using this
  simp [trivial_lie_zero]
/-
**RootPairing.GeckConstruction.** 是 Mathlib 中的一个实例，位于命名空间 `RootPairing.GeckConst
ruction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LieModule.IsTriangularizable R (cartanSubalgebra' b) (b.support ⊕ ι → R) := by
  refine ⟨fun ⟨⟨x, hx'⟩, hx⟩ ↦ ?_⟩
  obtain ⟨d, rfl⟩ : ∃ d : b.support ⊕ ι → R, Matrix.diagonal d = x :=
    span_range_h_le_range_diagonal <| by simpa using! hx
  simp
/-
**RootPairing.GeckConstruction.cartanSubalgebra_le_lieAlgebra** 是 Mathlib 中的一个引理
，位于命名空间 `RootPairing.GeckConstruction`。
形式化陈述：cartanSubalgebra_le_lieAlgebra : cartanSubalgebra b <= lieAlgebra b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RootPairing.GeckConstruction.cartanSubalgebra.eq_1`：∀ {ι : Type u_1} {R 
: Type u_2} {M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommG
roup M]   [inst_2 : _root_.Module R M] […
· 使用定理 `RootPairing.GeckConstruction.lieAlgebra.eq_1`：∀ {ι : Type u_1} {R : Type
 u_2} {M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M
]   [inst_2 : _root_.Module R M] […
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubalgebra.toSubmodule_le_toSubmodule`：toSubmodule_le_toSubmodule : (
K : Submodule R L) <= K' ↔ K <= K'
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `LieSubalgebra.subset_lieSpan`：subset_lieSpan : s subseteq lieSpan R L s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
lemma cartanSubalgebra_le_lieAlgebra :
    cartanSubalgebra b ≤ lieAlgebra b := by
  rw [cartanSubalgebra, lieAlgebra, ← LieSubalgebra.toSubmodule_le_toSubmodule, Submodule.span_le]
  rintro - ⟨i, rfl⟩
  exact LieSubalgebra.subset_lieSpan <| Or.inl <| Or.inl <| mem_range_self i
/-
**RootPairing.GeckConstruction.e_lie_u** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Ge
ckConstruction`。
形式化陈述：e_lie_u (i j : b.support) : ⁅e i, u j⁆ = |b.cartanMatrix i j| • v b i
参数：i j : b.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.mulVec_single`：mulVec_single [Fintype n] [DecidableEq n] [NonUnit
alNonAssocSemiring R] (M : Matrix m n R) (j : n) (x : R) : M *ᵥ Pi.single j x = 
MulOpposit…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `smul_ite`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a b : α) (c : β),   (c • if p then a else b) = if p the…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma e_lie_u (i j : b.support) :
    ⁅e i, u j⁆ = |b.cartanMatrix i j| • v b i := by
  ext (k | k) <;> simp [e, Pi.single_apply]
/-
**RootPairing.GeckConstruction.e_lie_v_ne** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing
.GeckConstruction`。
形式化陈述：e_lie_v_ne {i j : ι} {k : b.support} (h : P.root j = P.root k + P.root i) 
: ⁅e k, v b i⁆ = (P.chainBotCoeff k i + 1 : R) • v b j
参数：h : P.root j = P.root k + P.root i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `RootPairing.ne_zero`：ne_zero [NeZero (2 : R)] : (P.root i : M) != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `RootPairing.root_reflectionPerm`：root_reflectionPerm (j : ι) : P.root (P
.reflectionPerm i j) = (P.reflection i) (P.root j)
· 使用引理 `RootPairing.reflection_apply_self`：reflection_apply_self : P.reflection 
i (P.root i) = - P.root i
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.mulVec_single`：mulVec_single [Fintype n] [DecidableEq n] [NonUnit
alNonAssocSemiring R] (M : Matrix m n R) (j : n) (x : R) : M *ᵥ Pi.single j x = 
MulOpposit…
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Function.instEmbeddingLikeEmbedding`：∀ {α : Sort u} {β : Sort v}, Embedd
ingLike (α ↪ β) α β
· 使用定理 `smul_ite`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a b : α) (c : β),   (c • if p then a else b) = if p the…
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
（共 31 条，此处仅展示前 30 条）
-/
lemma e_lie_v_ne {i j : ι} {k : b.support} (h : P.root j = P.root k + P.root i) :
    ⁅e k, v b i⁆ = (P.chainBotCoeff k i + 1 : R) • v b j := by
  let := P.indexNeg
  ext (l | l)
  · replace h : i ≠ -k := by rintro rfl; exact P.ne_zero j <| by simpa using h
    simp [e, h, -indexNeg_neg]
  · simp [e, ← h, Pi.single_apply]
/-
**RootPairing.GeckConstruction.f_lie_v_same** 是 Mathlib 中的一个引理，位于命名空间 `RootPairi
ng.GeckConstruction`。
形式化陈述：f_lie_v_same (i : b.support) : ⁅f i, v b i⁆ = u i
参数：i : b.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.mulVec_single`：mulVec_single [Fintype n] [DecidableEq n] [NonUnit
alNonAssocSemiring R] (M : Matrix m n R) (j : n) (x : R) : M *ᵥ Pi.single j x = 
MulOpposit…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `smul_ite`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a b : α) (c : β),   (c • if p then a else b) = if p the…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
· 使用定理 `Sum.inl.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : α), (Sum.inl val
 = Sum.inl val_1) = (val = val_1)
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `RootPairing.ne_zero`：ne_zero [NeZero (2 : R)] : (P.root i : M) != 0
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma f_lie_v_same (i : b.support) :
    ⁅f i, v b i⁆ = u i := by
  ext (j | j)
  · simp [f, Pi.single_apply]
  · simp [f, P.ne_zero j]
/-
**RootPairing.GeckConstruction.f_lie_v_ne** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing
.GeckConstruction`。
形式化陈述：f_lie_v_ne {i j : ι} {k : b.support} (h : P.root i = P.root j + P.root k) 
: ⁅f k, v b i⁆ = (P.chainTopCoeff k i + 1 : R) • v b j
参数：h : P.root i = P.root j + P.root k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `RootPairing.ne_zero`：ne_zero [NeZero (2 : R)] : (P.root i : M) != 0
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.mulVec_single`：mulVec_single [Fintype n] [DecidableEq n] [NonUnit
alNonAssocSemiring R] (M : Matrix m n R) (j : n) (x : R) : M *ᵥ Pi.single j x = 
MulOpposit…
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `Function.instEmbeddingLikeEmbedding`：∀ {α : Sort u} {β : Sort v}, Embedd
ingLike (α ↪ β) α β
· 使用定理 `smul_ite`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a b : α) (c : β),   (c • if p then a else b) = if p the…
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
（共 31 条，此处仅展示前 30 条）
-/
lemma f_lie_v_ne {i j : ι} {k : b.support} (h : P.root i = P.root j + P.root k) :
    ⁅f k, v b i⁆ = (P.chainTopCoeff k i + 1 : R) • v b j := by
  ext (l | l)
  · replace h : i ≠ k := by rintro rfl; exact P.ne_zero j <| by simpa using h
    simp [f, h]
  · simp [f, h, Pi.single_apply]

section ωConj

variable (b) in
/-- The conjugation `x ↦ ωxω` as an equivalence of Lie algebras. -/
/-
**RootPairing.GeckConstruction.** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing.GeckConst
ruction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The conjugation `x ↦ ωxω` as an equivalence of Lie algebras.
-/
@[simps] def ωConj :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) R ≃ₗ⁅R⁆ Matrix (b.support ⊕ ι) (b.support ⊕ ι) R where
  toFun x := ω b * x * ω b
  invFun x := ω b * x * ω b
  map_add' x y := by noncomm_ring
  map_smul' t x := by simp
  map_lie' {x y} := by
    simp only [Ring.lie_def]
    nth_rw 1 [← mul_one x]
    nth_rw 2 [← one_mul x]
    simp only [← ω_mul_ω (b := b)]
    noncomm_ring
  left_inv x := by
    simp only [← mul_assoc, ω_mul_ω, one_mul]
    simp [mul_assoc]
  right_inv x := by
    simp only [← mul_assoc, ω_mul_ω, one_mul]
    simp [mul_assoc]
/-
**RootPairing.GeckConstruction.** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.GeckConst
ruction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ωConj_mem_of_mem
    {x : Matrix (b.support ⊕ ι) (b.support ⊕ ι) R} (hx : x ∈ lieAlgebra b) :
    ωConj b x ∈ lieAlgebra b := by
  induction hx using LieSubalgebra.lieSpan_induction with
  | mem u hu =>
    obtain (⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩) : (∃ j, h j = u) ∨ (∃ j, e j = u) ∨ (∃ j, f j = u) := by
      simpa only [mem_union, mem_range, or_assoc] using hu
    · rw [← neg_mem_iff]
      exact LieSubalgebra.subset_lieSpan <| by simp [ω_mul_h, mul_assoc]
    · exact LieSubalgebra.subset_lieSpan <| by simp [ω_mul_e, mul_assoc]
    · exact LieSubalgebra.subset_lieSpan <| by simp [ω_mul_f, mul_assoc]
  | zero => simp
  | add u v _ _ hu hv => simpa [mul_add, add_mul] using add_mem hu hv
  | smul t u _ hu => simpa using SMulMemClass.smul_mem _ hu
  | lie u v _ _ hu hv =>
    rw [LieEquiv.map_lie]
    exact (lieAlgebra b).lie_mem hu hv

variable (N : LieSubmodule R (lieAlgebra b) (b.support ⊕ ι → R))

/-- The equivalence `x ↦ ωxω` as an operation on Lie submodules of the Geck construction. -/
/-
**RootPairing.GeckConstruction.** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing.GeckConst
ruction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence `x ↦ ωxω` as an operation on Lie submodules of the Geck construc
tion.
-/
def ωConjLieSubmodule :
    LieSubmodule R (lieAlgebra b) (b.support ⊕ ι → R) where
  __ := N.toSubmodule.comap (ω b).toLin'
  lie_mem A {x} hx := by
    let A' : lieAlgebra b := ⟨ωConj b _, ωConj_mem_of_mem A.property⟩
    suffices ⁅A', ω b *ᵥ x⁆ ∈ N by simpa [A', mul_assoc] using this
    exact LieSubmodule.lie_mem _ hx
/-
**RootPairing.GeckConstruction.mem_** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.GeckC
onstruction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mem_ωConjLieSubmodule_iff {x : b.support ⊕ ι → R} :
    x ∈ ωConjLieSubmodule N ↔ (ω b) *ᵥ x ∈ N :=
  Iff.rfl
/-
**RootPairing.GeckConstruction.** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.GeckConst
ruction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ωConjLieSubmodule_eq_top_iff : ωConjLieSubmodule N = ⊤ ↔ N = ⊤ := by
  rw [← LieSubmodule.toSubmodule_eq_top]
  let e : Submodule R (b.support ⊕ ι → R) ≃o Submodule R (b.support ⊕ ι → R) :=
    Submodule.orderIsoMapComapOfBijective (ω b).toLin' (Involutive.bijective fun x ↦ by simp)
  change e.symm N = ⊤ ↔ _
  simp

end ωConj

end RootPairing.GeckConstruction

