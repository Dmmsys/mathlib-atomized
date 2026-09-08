/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!

# Some finiteness results of tensor product

This file contains some finiteness results of tensor product.

- `TensorProduct.exists_multiset`, `TensorProduct.exists_finsupp_left`,
  `TensorProduct.exists_finsupp_right`, `TensorProduct.exists_finset`:
  any element of `M ⊗[R] N` can be written as a finite sum of pure tensors.
  See also `TensorProduct.span_tmul_eq_top`.

- `TensorProduct.exists_finite_submodule_left_of_setFinite`,
  `TensorProduct.exists_finite_submodule_right_of_setFinite`,
  `TensorProduct.exists_finite_submodule_of_setFinite`:
  any finite subset of `M ⊗[R] N` is contained in `M' ⊗[R] N`,
  resp. `M ⊗[R] N'`, resp. `M' ⊗[R] N'`,
  for some finitely generated submodules `M'` and `N'` of `M` and `N`, respectively.

- `TensorProduct.exists_finite_submodule_left_of_setFinite'`,
  `TensorProduct.exists_finite_submodule_right_of_setFinite'`,
  `TensorProduct.exists_finite_submodule_of_setFinite'`:
  variation of the above results where `M` and `N` are already submodules.

## Tags

tensor product, finitely generated

-/

public section

open scoped TensorProduct

open Submodule

variable {R M N : Type*}

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

variable {M₁ M₂ : Submodule R M} {N₁ N₂ : Submodule R N}

namespace TensorProduct

/-- For any element `x` of `M ⊗[R] N`, there exists a (finite) multiset `{ (m_i, n_i) }`
of `M × N`, such that `x` is equal to the sum of `m_i ⊗ₜ[R] n_i`. -/
/-
**TensorProduct.exists_multiset** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：exists_multiset (x : M otimes[R] N) : exists S : Multiset (M × N), x = (S.
map fun i => i.1 otimesₜ[R] i.2).sum
参数：x : M otimes[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.sum_singleton`：∀ {M : Type u_3} [inst : AddCommMonoid M] (a : M
), {a}.sum = a
· 使用定理 `Multiset.map_add`：map_add (f : α -> β) (s t) : map f (s + t) = map f s +
 map f t
· 使用定理 `Multiset.sum_add`：∀ {M : Type u_5} [inst : AddCommMonoid M] (s t : Multi
set M), (s + t).sum = s.sum + t.sum

--- 原说明 ---
For any element `x` of `M ⊗[R] N`, there exists a (finite) multiset `{ (m_i, n_i
) }`
of `M × N`, such that `x` is equal to the sum of `m_i ⊗ₜ[R] n_i`.
-/
theorem exists_multiset (x : M ⊗[R] N) :
    ∃ S : Multiset (M × N), x = (S.map fun i ↦ i.1 ⊗ₜ[R] i.2).sum := by
  induction x with
  | zero => exact ⟨0, by simp⟩
  | tmul x y => exact ⟨{(x, y)}, by simp⟩
  | add x y hx hy =>
    obtain ⟨Sx, hx⟩ := hx
    obtain ⟨Sy, hy⟩ := hy
    exact ⟨Sx + Sy, by rw [Multiset.map_add, Multiset.sum_add, hx, hy]⟩

/-- For any element `x` of `M ⊗[R] N`, there exists a finite subset `{ (m_i, n_i) }`
of `M × N` such that each `m_i` is distinct (we represent it as an element of `M →₀ N`),
such that `x` is equal to the sum of `m_i ⊗ₜ[R] n_i`. -/
/-
**TensorProduct.exists_finsupp_left** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：exists_finsupp_left (x : M otimes[R] N) : exists S : M ->₀ N, x = S.sum fu
n m n => m otimesₜ[R] n
参数：x : M otimes[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.tmul_zero`：tmul_zero (m : M) : m otimesₜ[R] (0 : N) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.sum_add_index'`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} 
[inst : AddZeroClass M] [inst_1 : AddCommMonoid N] {f g : α →₀ M}   {h : α → M →
 N},   (∀ (a…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `TensorProduct.tmul_add`：tmul_add (m : M) (n₁ n₂ : N) : m otimesₜ (n₁ + n
₂) = m otimesₜ n₁ + m otimesₜ[R] n₂

--- 原说明 ---
For any element `x` of `M ⊗[R] N`, there exists a finite subset `{ (m_i, n_i) }`
of `M × N` such that each `m_i` is distinct (we represent it as an element of `M
 →₀ N`),
such that `x` is equal to the sum of `m_i ⊗ₜ[R] n_i`.
-/
theorem exists_finsupp_left (x : M ⊗[R] N) :
    ∃ S : M →₀ N, x = S.sum fun m n ↦ m ⊗ₜ[R] n := by
  induction x with
  | zero => exact ⟨0, by simp⟩
  | tmul x y => exact ⟨Finsupp.single x y, by simp⟩
  | add x y hx hy =>
    obtain ⟨Sx, hx⟩ := hx
    obtain ⟨Sy, hy⟩ := hy
    use Sx + Sy
    rw [hx, hy]
    exact (Finsupp.sum_add_index' (by simp) TensorProduct.tmul_add).symm

/-- For any element `x` of `M ⊗[R] N`, there exists a finite subset `{ (m_i, n_i) }`
of `M × N` such that each `n_i` is distinct (we represent it as an element of `N →₀ M`),
such that `x` is equal to the sum of `m_i ⊗ₜ[R] n_i`. -/
/-
**TensorProduct.exists_finsupp_right** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：exists_finsupp_right (x : M otimes[R] N) : exists S : N ->₀ M, x = S.sum f
un n m => m otimesₜ[R] n
参数：x : M otimes[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.exists_finsupp_left`：exists_finsupp_left (x : M otimes[R] 
N) : exists S : M ->₀ N, x = S.sum fun m n => m otimesₜ[R] n
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
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
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
For any element `x` of `M ⊗[R] N`, there exists a finite subset `{ (m_i, n_i) }`
of `M × N` such that each `n_i` is distinct (we represent it as an element of `N
 →₀ M`),
such that `x` is equal to the sum of `m_i ⊗ₜ[R] n_i`.
-/
theorem exists_finsupp_right (x : M ⊗[R] N) :
    ∃ S : N →₀ M, x = S.sum fun n m ↦ m ⊗ₜ[R] n := by
  obtain ⟨S, h⟩ := exists_finsupp_left (TensorProduct.comm R M N x)
  refine ⟨S, (TensorProduct.comm R M N).injective ?_⟩
  simp_rw [h, Finsupp.sum, map_sum, comm_tmul]

/-- For any element `x` of `M ⊗[R] N`, there exists a finite subset `{ (m_i, n_i) }`
of `M × N`, such that `x` is equal to the sum of `m_i ⊗ₜ[R] n_i`. -/
/-
**TensorProduct.exists_finset** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：exists_finset (x : M otimes[R] N) : exists S : Finset (M × N), x = S.sum f
un i => i.1 otimesₜ[R] i.2
参数：x : M otimes[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.exists_finsupp_left`：exists_finsupp_left (x : M otimes[R] 
N) : exists S : M ->₀ N, x = S.sum fun m n => m otimesₜ[R] n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.sum.eq_1`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [inst 
: Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M) (g : α → M → N),   f.sum g = ∑
 a ∈ f…
· 使用定理 `Finset.sum_nbij'`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst :
 AddCommMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M}   {g : κ → M} (i : ι
 → κ) …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)

--- 原说明 ---
For any element `x` of `M ⊗[R] N`, there exists a finite subset `{ (m_i, n_i) }`
of `M × N`, such that `x` is equal to the sum of `m_i ⊗ₜ[R] n_i`.
-/
theorem exists_finset (x : M ⊗[R] N) :
    ∃ S : Finset (M × N), x = S.sum fun i ↦ i.1 ⊗ₜ[R] i.2 := by
  obtain ⟨S, h⟩ := exists_finsupp_left x
  use S.graph
  rw [h, Finsupp.sum]
  apply Finset.sum_nbij' (fun m ↦ ⟨m, S m⟩) Prod.fst <;> simp

/-- For a finite subset `s` of `M ⊗[R] N`, there are finitely generated
submodules `M'` and `N'` of `M` and `N`, respectively, such that `s` is contained in the image
of `M' ⊗[R] N'` in `M ⊗[R] N`.

In particular, every element of a tensor product lies in the tensor product of some finite
submodules. -/
/-
**TensorProduct.exists_finite_submodule_of_setFinite** 是 Mathlib 中的一个定理，位于命名空间 `
TensorProduct`。
形式化陈述：exists_finite_submodule_of_setFinite (s : Set (M otimes[R] N)) (hs : s.Fin
ite) : exists (M' : Submodule R M) (N' : Submodule R N), Module.Finite R M' ∧ Mo
dule.Finite R N' ∧ s subseteq LinearMap.range (mapIncl M' N')
参数：s : Set (M otimes[R] N)；hs : s.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.Finite.induction_on`：∀ {α : Type u} {motive : (s : Set α) → s.Finite
 → Prop} (s : Set α) (hs : s.Finite),   motive ∅ ⋯ → (∀ {a : α} {s : Set α}, a ∉
 s → ∀ (hs : …
· 使用定理 `Submodule.fg_bot`：fg_bot : (⊥ : Submodule R M).FG
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `Set.insert_subset`：insert_subset (ha : a in t) (hs : s subseteq t) : ins
ert a s subseteq t
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `Submodule.FG.sup`：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N₁ N₂ : Submodule R M},
 N₁.FG…
· 使用定理 `Submodule.fg_span_singleton`：fg_span_singleton (x : M) : FG (R ∙ x)
· 使用定理 `Submodule.mem_sup_right`：mem_sup_right {S T : Submodule R M} : forall {x
 : M}, x in T -> x in S ⊔ T
· 使用定理 `Submodule.mem_span_singleton_self`：mem_span_singleton_self (x : M) : x i
n R ∙ x
· 使用引理 `TensorProduct.range_mapIncl_mono`：range_mapIncl_mono {p p' : Submodule R
 P} {q q' : Submodule R Q} (hp : p <= p') (hq : q <= q') : LinearMap.range (mapI
ncl p q) <= LinearMap.…
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s

--- 原说明 ---
For a finite subset `s` of `M ⊗[R] N`, there are finitely generated
submodules `M'` and `N'` of `M` and `N`, respectively, such that `s` is containe
d in the image
of `M' ⊗[R] N'` in `M ⊗[R] N`.

In particular, every element of a tensor product lies in the tensor product of s
ome finite
submodules.
-/
theorem exists_finite_submodule_of_setFinite (s : Set (M ⊗[R] N)) (hs : s.Finite) :
    ∃ (M' : Submodule R M) (N' : Submodule R N), Module.Finite R M' ∧ Module.Finite R N' ∧
      s ⊆ LinearMap.range (mapIncl M' N') := by
  simp_rw [Module.Finite.iff_fg]
  induction s, hs using Set.Finite.induction_on with
  | empty => exact ⟨_, _, fg_bot, fg_bot, Set.empty_subset _⟩
  | @insert a s _ _ ih =>
  obtain ⟨M', N', hM', hN', h⟩ := ih
  refine TensorProduct.induction_on a ?_ (fun x y ↦ ?_) fun x y hx hy ↦ ?_
  · exact ⟨M', N', hM', hN', Set.insert_subset (zero_mem _) h⟩
  · refine ⟨_, _, hM'.sup (fg_span_singleton x),
      hN'.sup (fg_span_singleton y), Set.insert_subset ?_ fun z hz ↦ ?_⟩
    · exact ⟨⟨x, mem_sup_right (mem_span_singleton_self x)⟩ ⊗ₜ
        ⟨y, mem_sup_right (mem_span_singleton_self y)⟩, rfl⟩
    · exact range_mapIncl_mono le_sup_left le_sup_left (h hz)
  · obtain ⟨M₁', N₁', hM₁', hN₁', h₁⟩ := hx
    obtain ⟨M₂', N₂', hM₂', hN₂', h₂⟩ := hy
    refine ⟨_, _, hM₁'.sup hM₂', hN₁'.sup hN₂', Set.insert_subset (add_mem ?_ ?_) fun z hz ↦ ?_⟩
    · exact range_mapIncl_mono le_sup_left le_sup_left (h₁ (Set.mem_insert x s))
    · exact range_mapIncl_mono le_sup_right le_sup_right (h₂ (Set.mem_insert y s))
    · exact range_mapIncl_mono le_sup_left le_sup_left (h₁ (Set.subset_insert x s hz))

/-- For a finite subset `s` of `M ⊗[R] N`, there exists a finitely generated
submodule `M'` of `M`, such that `s` is contained in the image
of `M' ⊗[R] N` in `M ⊗[R] N`. -/
/-
**TensorProduct.exists_finite_submodule_left_of_setFinite** 是 Mathlib 中的一个定理，位于命
名空间 `TensorProduct`。
形式化陈述：exists_finite_submodule_left_of_setFinite (s : Set (M otimes[R] N)) (hs : 
s.Finite) : exists M' : Submodule R M, Module.Finite R M' ∧ s subseteq LinearMap
.range (M'.subtype.rTensor N)
参数：s : Set (M otimes[R] N)；hs : s.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.exists_finite_submodule_of_setFinite`：exists_finite_submod
ule_of_setFinite (s : Set (M otimes[R] N)) (hs : s.Finite) : exists (M' : Submod
ule R M) (N' : Submodule R N), Module.Fi…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.rTensor_comp_lTensor`：rTensor_comp_lTensor (f : M ->ₗ[R] P) (g
 : N ->ₗ[R] Q) : (f.rTensor Q).comp (g.lTensor M) = map f g
· 使用定理 `TensorProduct.mapIncl.eq_1`：∀ {R : Type u_1} [inst : CommSemiring R] {P 
: Type u_9} {Q : Type u_10} [inst_1 : AddCommMonoid P]   [inst_2 : AddCommMonoid
 Q] [inst_3 : _r…
· 使用定理 `LinearMap.range_comp_le_range`：range_comp_le_range [RingHomSurjective τ₂
₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : range (g
.comp f : M ->ₛₗ[τ₁…

--- 原说明 ---
For a finite subset `s` of `M ⊗[R] N`, there exists a finitely generated
submodule `M'` of `M`, such that `s` is contained in the image
of `M' ⊗[R] N` in `M ⊗[R] N`.
-/
theorem exists_finite_submodule_left_of_setFinite (s : Set (M ⊗[R] N)) (hs : s.Finite) :
    ∃ M' : Submodule R M, Module.Finite R M' ∧ s ⊆ LinearMap.range (M'.subtype.rTensor N) := by
  obtain ⟨M', _, hfin, _, h⟩ := exists_finite_submodule_of_setFinite s hs
  refine ⟨M', hfin, ?_⟩
  rw [mapIncl, ← LinearMap.rTensor_comp_lTensor] at h
  exact h.trans (LinearMap.range_comp_le_range _ _)

/-- For a finite subset `s` of `M ⊗[R] N`, there exists a finitely generated
submodule `N'` of `N`, such that `s` is contained in the image
of `M ⊗[R] N'` in `M ⊗[R] N`. -/
/-
**TensorProduct.exists_finite_submodule_right_of_setFinite** 是 Mathlib 中的一个定理，位于
命名空间 `TensorProduct`。
形式化陈述：exists_finite_submodule_right_of_setFinite (s : Set (M otimes[R] N)) (hs :
 s.Finite) : exists N' : Submodule R N, Module.Finite R N' ∧ s subseteq LinearMa
p.range (N'.subtype.lTensor M)
参数：s : Set (M otimes[R] N)；hs : s.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.exists_finite_submodule_of_setFinite`：exists_finite_submod
ule_of_setFinite (s : Set (M otimes[R] N)) (hs : s.Finite) : exists (M' : Submod
ule R M) (N' : Submodule R N), Module.Fi…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.lTensor_comp_rTensor`：lTensor_comp_rTensor (f : M ->ₗ[R] P) (g
 : N ->ₗ[R] Q) : (g.lTensor P).comp (f.rTensor N) = map f g
· 使用定理 `TensorProduct.mapIncl.eq_1`：∀ {R : Type u_1} [inst : CommSemiring R] {P 
: Type u_9} {Q : Type u_10} [inst_1 : AddCommMonoid P]   [inst_2 : AddCommMonoid
 Q] [inst_3 : _r…
· 使用定理 `LinearMap.range_comp_le_range`：range_comp_le_range [RingHomSurjective τ₂
₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : range (g
.comp f : M ->ₛₗ[τ₁…

--- 原说明 ---
For a finite subset `s` of `M ⊗[R] N`, there exists a finitely generated
submodule `N'` of `N`, such that `s` is contained in the image
of `M ⊗[R] N'` in `M ⊗[R] N`.
-/
theorem exists_finite_submodule_right_of_setFinite (s : Set (M ⊗[R] N)) (hs : s.Finite) :
    ∃ N' : Submodule R N, Module.Finite R N' ∧ s ⊆ LinearMap.range (N'.subtype.lTensor M) := by
  obtain ⟨_, N', _, hfin, h⟩ := exists_finite_submodule_of_setFinite s hs
  refine ⟨N', hfin, ?_⟩
  rw [mapIncl, ← LinearMap.lTensor_comp_rTensor] at h
  exact h.trans (LinearMap.range_comp_le_range _ _)

/-- Variation of `TensorProduct.exists_finite_submodule_of_setFinite` where `M` and `N` are
already submodules. -/
/-
**TensorProduct.exists_finite_submodule_of_setFinite'** 是 Mathlib 中的一个定理，位于命名空间 
`TensorProduct`。
形式化陈述：exists_finite_submodule_of_setFinite' (s : Set (M₁ otimes[R] N₁)) (hs : s.
Finite) : exists (M' : Submodule R M) (N' : Submodule R N) (hM : M' <= M₁) (hN :
 N' <= N₁), Module.Finite R M' ∧ Module.Finite R N' ∧ s subseteq LinearMap.range
 (TensorProduct.map (inclusion hM) (inclusion hN))
参数：s : Set (M₁ otimes[R] N₁)；hs : s.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.exists_finite_submodule_of_setFinite`：exists_finite_submod
ule_of_setFinite (s : Set (M otimes[R] N)) (hs : s.Finite) : exists (M' : Submod
ule R M) (N' : Submodule R N), Module.Fi…
· 使用定理 `Submodule.map_subtype_le`：map_subtype_le (p' : Submodule R p) : map p.su
btype p' <= p
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.map_comp`：map_comp (f₂ : M₂ ->ₛₗ[σ₂₃] M₃) (g₂ : N₂ ->ₛₗ[σ₂
₃] N₃) (f₁ : M ->ₛₗ[σ₁₂] M₂) (g₁ : N ->ₛₗ[σ₁₂] N₂) : map (f₂ ∘ₛₗ f₁) (g₂ ∘ₛₗ g₁)
 = (map f₂ g…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `TensorProduct.mapIncl.eq_1`：∀ {R : Type u_1} [inst : CommSemiring R] {P 
: Type u_9} {Q : Type u_10} [inst_1 : AddCommMonoid P]   [inst_2 : AddCommMonoid
 Q] [inst_3 : _r…
· 使用定理 `LinearMap.range_comp_le_range`：range_comp_le_range [RingHomSurjective τ₂
₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : range (g
.comp f : M ->ₛₗ[τ₁…

--- 原说明 ---
Variation of `TensorProduct.exists_finite_submodule_of_setFinite` where `M` and 
`N` are
already submodules.
-/
theorem exists_finite_submodule_of_setFinite' (s : Set (M₁ ⊗[R] N₁)) (hs : s.Finite) :
    ∃ (M' : Submodule R M) (N' : Submodule R N) (hM : M' ≤ M₁) (hN : N' ≤ N₁),
      Module.Finite R M' ∧ Module.Finite R N' ∧
        s ⊆ LinearMap.range (TensorProduct.map (inclusion hM) (inclusion hN)) := by
  obtain ⟨M', N', _, _, h⟩ := exists_finite_submodule_of_setFinite s hs
  have hM := map_subtype_le M₁ M'
  have hN := map_subtype_le N₁ N'
  refine ⟨_, _, hM, hN, .map _ _, .map _ _, ?_⟩
  rw [mapIncl,
    show M'.subtype = inclusion hM ∘ₗ M₁.subtype.submoduleMap M' by ext; simp,
    show N'.subtype = inclusion hN ∘ₗ N₁.subtype.submoduleMap N' by ext; simp,
    map_comp] at h
  exact h.trans (LinearMap.range_comp_le_range _ _)

/-- Variation of `TensorProduct.exists_finite_submodule_left_of_setFinite` where `M` and `N` are
already submodules. -/
/-
**TensorProduct.exists_finite_submodule_left_of_setFinite'** 是 Mathlib 中的一个定理，位于
命名空间 `TensorProduct`。
形式化陈述：exists_finite_submodule_left_of_setFinite' (s : Set (M₁ otimes[R] N₁)) (hs
 : s.Finite) : exists (M' : Submodule R M) (hM : M' <= M₁), Module.Finite R M' ∧
 s subseteq LinearMap.range ((inclusion hM).rTensor N₁)
参数：s : Set (M₁ otimes[R] N₁)；hs : s.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.exists_finite_submodule_of_setFinite'`：exists_finite_submo
dule_of_setFinite' (s : Set (M₁ otimes[R] N₁)) (hs : s.Finite) : exists (M' : Su
bmodule R M) (N' : Submodule R N) (hM : M…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.rTensor_comp_lTensor`：rTensor_comp_lTensor (f : M ->ₗ[R] P) (g
 : N ->ₗ[R] Q) : (f.rTensor Q).comp (g.lTensor M) = map f g
· 使用定理 `LinearMap.range_comp_le_range`：range_comp_le_range [RingHomSurjective τ₂
₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : range (g
.comp f : M ->ₛₗ[τ₁…

--- 原说明 ---
Variation of `TensorProduct.exists_finite_submodule_left_of_setFinite` where `M`
 and `N` are
already submodules.
-/
theorem exists_finite_submodule_left_of_setFinite' (s : Set (M₁ ⊗[R] N₁)) (hs : s.Finite) :
    ∃ (M' : Submodule R M) (hM : M' ≤ M₁), Module.Finite R M' ∧
      s ⊆ LinearMap.range ((inclusion hM).rTensor N₁) := by
  obtain ⟨M', _, hM, _, hfin, _, h⟩ := exists_finite_submodule_of_setFinite' s hs
  refine ⟨M', hM, hfin, ?_⟩
  rw [← LinearMap.rTensor_comp_lTensor] at h
  exact h.trans (LinearMap.range_comp_le_range _ _)

/-- Variation of `TensorProduct.exists_finite_submodule_right_of_setFinite` where `M` and `N` are
already submodules. -/
/-
**TensorProduct.exists_finite_submodule_right_of_setFinite'** 是 Mathlib 中的一个定理，位
于命名空间 `TensorProduct`。
形式化陈述：exists_finite_submodule_right_of_setFinite' (s : Set (M₁ otimes[R] N₁)) (h
s : s.Finite) : exists (N' : Submodule R N) (hN : N' <= N₁), Module.Finite R N' 
∧ s subseteq LinearMap.range ((inclusion hN).lTensor M₁)
参数：s : Set (M₁ otimes[R] N₁)；hs : s.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.exists_finite_submodule_of_setFinite'`：exists_finite_submo
dule_of_setFinite' (s : Set (M₁ otimes[R] N₁)) (hs : s.Finite) : exists (M' : Su
bmodule R M) (N' : Submodule R N) (hM : M…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.lTensor_comp_rTensor`：lTensor_comp_rTensor (f : M ->ₗ[R] P) (g
 : N ->ₗ[R] Q) : (g.lTensor P).comp (f.rTensor N) = map f g
· 使用定理 `LinearMap.range_comp_le_range`：range_comp_le_range [RingHomSurjective τ₂
₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : range (g
.comp f : M ->ₛₗ[τ₁…

--- 原说明 ---
Variation of `TensorProduct.exists_finite_submodule_right_of_setFinite` where `M
` and `N` are
already submodules.
-/
theorem exists_finite_submodule_right_of_setFinite' (s : Set (M₁ ⊗[R] N₁)) (hs : s.Finite) :
    ∃ (N' : Submodule R N) (hN : N' ≤ N₁), Module.Finite R N' ∧
      s ⊆ LinearMap.range ((inclusion hN).lTensor M₁) := by
  obtain ⟨_, N', _, hN, _, hfin, h⟩ := exists_finite_submodule_of_setFinite' s hs
  refine ⟨N', hN, hfin, ?_⟩
  rw [← LinearMap.lTensor_comp_rTensor] at h
  exact h.trans (LinearMap.range_comp_le_range _ _)

/-- Avoid using this and use the induction principle on `M ⊗[R] N` instead. -/
/-
**TensorProduct.exists_sum_tmul_eq** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
形式化陈述：exists_sum_tmul_eq (x : M otimes[R] N) : exists (k : Nat) (m : Fin k -> M)
 (n : Fin k -> N), x = ∑ j, m j otimesₜ n j
参数：x : M otimes[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.univ_eq_empty`：univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Fin.sum_univ_add`：∀ {M : Type u_2} [inst : AddCommMonoid M] {a b : ℕ} (f
 : Fin (a + b) → M),   ∑ i, f i = ∑ i, f (Fin.castAdd b i) + ∑ i, f (Fin.natAdd 
a i)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fin.addCases_left`：∀ {m n : ℕ} {motive : Fin (m + n) → Sort u_1} {left :
 (i : Fin m) → motive (Fin.castAdd n i)}   {right : (i : Fin n) → motive (Fin.na
tAdd m …
· 使用定理 `Fin.addCases_right`：∀ {m n : ℕ} {motive : Fin (m + n) → Sort u_1} {left 
: (i : Fin m) → motive (Fin.castAdd n i)}   {right : (i : Fin n) → motive (Fin.n
atAdd m …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Avoid using this and use the induction principle on `M ⊗[R] N` instead.
-/
lemma exists_sum_tmul_eq (x : M ⊗[R] N) :
    ∃ (k : ℕ) (m : Fin k → M) (n : Fin k → N), x = ∑ j, m j ⊗ₜ n j := by
  induction x with
  | zero => exact ⟨0, IsEmpty.elim inferInstance, IsEmpty.elim inferInstance, by simp⟩
  | tmul x y => exact ⟨1, fun _ ↦ x, fun _ ↦ y, by simp⟩
  | add x y hx hy =>
    obtain ⟨kx, mx, nx, rfl⟩ := hx
    obtain ⟨ky, my, ny, rfl⟩ := hy
    use kx + ky, Fin.addCases mx my, Fin.addCases nx ny
    simp [Fin.sum_univ_add]

end TensorProduct

