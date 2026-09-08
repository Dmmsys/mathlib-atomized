/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.Basis
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Matrix results for barycentric co-ordinates

Results about the matrix of barycentric co-ordinates for a family of points in an affine space, with
respect to some affine basis.
-/

@[expose] public section


open Affine Matrix

open Set

universe u₁ u₂ u₃ u₄

variable {ι : Type u₁} {k : Type u₂} {V : Type u₃} {P : Type u₄}
variable [AddCommGroup V] [AffineSpace V P]

namespace AffineBasis

section Ring

variable [Ring k] [Module k V] (b : AffineBasis ι k P)

/-- Given an affine basis `p`, and a family of points `q : ι' → P`, this is the matrix whose
rows are the barycentric coordinates of `q` with respect to `p`.

It is an affine equivalent of `Basis.toMatrix`. -/
/-
**AffineBasis.toMatrix** 是 Mathlib 中的一个定义，位于命名空间 `AffineBasis`。
形式化陈述：toMatrix {ι' : Type*} (q : ι' -> P) : Matrix ι' ι k
参数：q : ι' -> P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an affine basis `p`, and a family of points `q : ι' → P`, this is the matr
ix whose
rows are the barycentric coordinates of `q` with respect to `p`.

It is an affine equivalent of `Basis.toMatrix`.
-/
noncomputable def toMatrix {ι' : Type*} (q : ι' → P) : Matrix ι' ι k :=
  fun i j => b.coord j (q i)

@[simp]
/-
**AffineBasis.toMatrix_apply** 是 Mathlib 中的一个定理，位于命名空间 `AffineBasis`。
形式化陈述：toMatrix_apply {ι' : Type*} (q : ι' -> P) (i : ι') (j : ι) : b.toMatrix q 
i j = b.coord j (q i)
参数：q : ι' -> P；i : ι'；j : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toMatrix_apply {ι' : Type*} (q : ι' → P) (i : ι') (j : ι) :
    b.toMatrix q i j = b.coord j (q i) := rfl

@[simp]
/-
**AffineBasis.toMatrix_self** 是 Mathlib 中的一个定理，位于命名空间 `AffineBasis`。
形式化陈述：toMatrix_self [DecidableEq ι] : b.toMatrix b = (1 : Matrix ι ι k)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineBasis.toMatrix_apply`：toMatrix_apply {ι' : Type*} (q : ι' -> P) (i
 : ι') (j : ι) : b.toMatrix q i j = b.coord j (q i)
· 使用定理 `AffineBasis.coord_apply`：coord_apply [DecidableEq ι] (i j : ι) : b.coord
 i (b j) = if i = j then 1 else 0
· 使用定理 `Matrix.one_eq_pi_single`：one_eq_pi_single {i j} : (1 : Matrix n n α) i j
 = Pi.single (M
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
-/
theorem toMatrix_self [DecidableEq ι] : b.toMatrix b = (1 : Matrix ι ι k) := by
  ext i j
  rw [toMatrix_apply, coord_apply, Matrix.one_eq_pi_single, Pi.single_apply]

variable {ι' : Type*}
/-
**AffineBasis.toMatrix_row_sum_one** 是 Mathlib 中的一个定理，位于命名空间 `AffineBasis`。
形式化陈述：toMatrix_row_sum_one [Fintype ι] (q : ι' -> P) (i : ι') : ∑ j, b.toMatrix 
q i j = 1
参数：q : ι' -> P；i : ι'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineBasis.sum_coord_apply_eq_one`：sum_coord_apply_eq_one [Fintype ι] (
q : P) : ∑ i, b.coord i q = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toMatrix_row_sum_one [Fintype ι] (q : ι' → P) (i : ι') : ∑ j, b.toMatrix q i j = 1 := by
  simp

/-- Given a family of points `p : ι' → P` and an affine basis `b`, if the matrix whose rows are the
coordinates of `p` with respect `b` has a right inverse, then `p` is affine independent. -/
/-
**AffineBasis.affineIndependent_of_toMatrix_right_inv** 是 Mathlib 中的一个定理，位于命名空间 
`AffineBasis`。
形式化陈述：affineIndependent_of_toMatrix_right_inv [Fintype ι] [Finite ι'] [Decidable
Eq ι'] (p : ι' -> P) {A : Matrix ι ι' k} (hA : b.toMatrix p * A = 1) : AffineInd
ependent k p
参数：p : ι' -> P；hA : b.toMatrix p * A = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `affineIndependent_iff_eq_of_fintype_affineCombination_eq`：affineIndepend
ent_iff_eq_of_fintype_affineCombination_eq [Fintype ι] (p : ι -> P) : AffineInde
pendent k p ↔ forall w1 w2 : ι -> k, ∑ i, w1 i…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.affineCombination_eq_linear_combination`：affineCombination_eq_lin
ear_combination (s : Finset ι) (p : ι -> V) (w : ι -> k) (hw : ∑ i in s, w i = 1
) : s.affineCombination k p w = ∑ i …
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `Finset.map_affineCombination`：map_affineCombination {V₂ P₂ : Type*} [Add
CommGroup V₂] [Module k V₂] [AffineSpace V₂ P₂] (p : ι -> P) (w : ι -> k) (hw : 
s.sum w = 1) (f : …
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.vecMul_vecMul`：vecMul_vecMul [Fintype n] [Fintype m] (v : m -> α)
 (M : Matrix m n α) (N : Matrix n o α) : v ᵥ* M ᵥ* N = v ᵥ* (M * N)
· 使用定理 `Matrix.vecMul_one`：vecMul_one (v : m -> α) : v ᵥ* 1 = v

--- 原说明 ---
Given a family of points `p : ι' → P` and an affine basis `b`, if the matrix who
se rows are the
coordinates of `p` with respect `b` has a right inverse, then `p` is affine inde
pendent.
-/
theorem affineIndependent_of_toMatrix_right_inv [Fintype ι] [Finite ι'] [DecidableEq ι']
    (p : ι' → P) {A : Matrix ι ι' k} (hA : b.toMatrix p * A = 1) : AffineIndependent k p := by
  cases nonempty_fintype ι'
  rw [affineIndependent_iff_eq_of_fintype_affineCombination_eq]
  intro w₁ w₂ hw₁ hw₂ hweq
  have hweq' : w₁ ᵥ* b.toMatrix p = w₂ ᵥ* b.toMatrix p := by
    ext j
    change (∑ i, w₁ i • b.coord j (p i)) = ∑ i, w₂ i • b.coord j (p i)
    rw [← Finset.univ.affineCombination_eq_linear_combination _ _ hw₁,
      ← Finset.univ.affineCombination_eq_linear_combination _ _ hw₂,
      ← Function.comp_def (b.coord j) p, ← Finset.univ.map_affineCombination p w₁ hw₁,
      ← Finset.univ.map_affineCombination p w₂ hw₂, hweq]
  replace hweq' := congr_arg (fun w => w ᵥ* A) hweq'
  simpa only [Matrix.vecMul_vecMul, hA, Matrix.vecMul_one] using hweq'

/-- Given a family of points `p : ι' → P` and an affine basis `b`, if the matrix whose rows are the
coordinates of `p` with respect `b` has a left inverse, then `p` spans the entire space. -/
/-
**AffineBasis.affineSpan_eq_top_of_toMatrix_left_inv** 是 Mathlib 中的一个定理，位于命名空间 `
AffineBasis`。
形式化陈述：affineSpan_eq_top_of_toMatrix_left_inv [Finite ι] [Fintype ι'] [DecidableE
q ι] [Nontrivial k] (p : ι' -> P) {A : Matrix ι ι' k} (hA : A * b.toMatrix p = 1
) : affineSpan k (range p) = ⊤
参数：p : ι' -> P；hA : A * b.toMatrix p = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `AffineBasis.sum_coord_apply_eq_one`：sum_coord_apply_eq_one [Fintype ι] (
q : P) : ∑ i, b.coord i q = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Finset.sum_comm`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst : 
AddCommMonoid β] {s : Finset γ} {t : Finset α} {f : γ → α → β},   ∑ x ∈ s, ∑ y ∈
 t, f…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `AffineBasis.ext_elem`：ext_elem [Finite ι] {q₁ q₂ : P} (h : forall i, b.c
oord i q₁ = b.coord i q₂) : q₁ = q₂
· 使用定理 `AffineBasis.coord_apply`：coord_apply [DecidableEq ι] (i j : ι) : b.coord
 i (b j) = if i = j then 1 else 0
· 使用定理 `Finset.map_affineCombination`：map_affineCombination {V₂ P₂ : Type*} [Add
CommGroup V₂] [Module k V₂] [AffineSpace V₂ P₂] (p : ι -> P) (w : ι -> k) (hw : 
s.sum w = 1) (f : …
· 使用定理 `Finset.affineCombination_eq_linear_combination`：affineCombination_eq_lin
ear_combination (s : Finset ι) (p : ι -> V) (w : ι -> k) (hw : ∑ i in s, w i = 1
) : s.affineCombination k p w = ∑ i …
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `affineCombination_mem_affineSpan`：affineCombination_mem_affineSpan [Nont
rivial k] {s : Finset ι} {w : ι -> k} (h : ∑ i in s, w i = 1) (p : ι -> P) : s.a
ffineCombination k p w…
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineBasis.tot`：tot : affineSpan k (range b) = ⊤
· 使用定理 `affineSpan_le`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_3} [inst : Ri
ng k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [S : AddTorsor V 
P] …

--- 原说明 ---
Given a family of points `p : ι' → P` and an affine basis `b`, if the matrix who
se rows are the
coordinates of `p` with respect `b` has a left inverse, then `p` spans the entir
e space.
-/
theorem affineSpan_eq_top_of_toMatrix_left_inv [Finite ι] [Fintype ι'] [DecidableEq ι]
    [Nontrivial k] (p : ι' → P) {A : Matrix ι ι' k} (hA : A * b.toMatrix p = 1) :
    affineSpan k (range p) = ⊤ := by
  cases nonempty_fintype ι
  suffices ∀ i, b i ∈ affineSpan k (range p) by
    rw [eq_top_iff, ← b.tot, affineSpan_le]
    rintro q ⟨i, rfl⟩
    exact this i
  intro i
  have hAi : ∑ j, A i j = 1 := by
    calc
      ∑ j, A i j = ∑ j, A i j * ∑ l, b.toMatrix p j l := by simp
      _ = ∑ j, ∑ l, A i j * b.toMatrix p j l := by simp_rw [Finset.mul_sum]
      _ = ∑ l, ∑ j, A i j * b.toMatrix p j l := by rw [Finset.sum_comm]
      _ = ∑ l, (A * b.toMatrix p) i l := rfl
      _ = 1 := by simp [hA, Matrix.one_apply]
  have hbi : b i = Finset.univ.affineCombination k p (A i) := by
    apply b.ext_elem
    intro j
    rw [b.coord_apply, Finset.univ.map_affineCombination _ _ hAi,
      Finset.univ.affineCombination_eq_linear_combination _ _ hAi]
    change _ = (A * b.toMatrix p) i j
    simp_rw [hA, Matrix.one_apply, @eq_comm _ i j]
  rw [hbi]
  exact affineCombination_mem_affineSpan hAi p

variable [Fintype ι] (b₂ : AffineBasis ι k P)

/-- A change of basis formula for barycentric coordinates.

See also `AffineBasis.toMatrix_inv_vecMul_toMatrix`. -/
@[simp]
/-
**AffineBasis.toMatrix_vecMul_coords** 是 Mathlib 中的一个定理，位于命名空间 `AffineBasis`。
形式化陈述：toMatrix_vecMul_coords (x : P) : b₂.coords x ᵥ* b.toMatrix b₂ = b.coords x
参数：x : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineBasis.affineCombination_coord_eq_self`：affineCombination_coord_eq_
self [Fintype ι] (q : P) : (Finset.univ.affineCombination k b fun i => b.coord i
 q) = q
· 使用定理 `Finset.map_affineCombination`：map_affineCombination {V₂ P₂ : Type*} [Add
CommGroup V₂] [Module k V₂] [AffineSpace V₂ P₂] (p : ι -> P) (w : ι -> k) (hw : 
s.sum w = 1) (f : …
· 使用定理 `AffineBasis.sum_coord_apply_eq_one`：sum_coord_apply_eq_one [Fintype ι] (
q : P) : ∑ i, b.coord i q = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.affineCombination_eq_linear_combination`：affineCombination_eq_lin
ear_combination (s : Finset ι) (p : ι -> V) (w : ι -> k) (hw : ∑ i in s, w i = 1
) : s.affineCombination k p w = ∑ i …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…

--- 原说明 ---
A change of basis formula for barycentric coordinates.

See also `AffineBasis.toMatrix_inv_vecMul_toMatrix`.
-/
theorem toMatrix_vecMul_coords (x : P) : b₂.coords x ᵥ* b.toMatrix b₂ = b.coords x := by
  ext j
  change _ = b.coord j x
  conv_rhs => rw [← b₂.affineCombination_coord_eq_self x]
  rw [Finset.map_affineCombination _ _ _ (b₂.sum_coord_apply_eq_one x)]
  simp [Matrix.vecMul, dotProduct, toMatrix_apply, coords]

variable [DecidableEq ι]
/-
**AffineBasis.toMatrix_mul_toMatrix** 是 Mathlib 中的一个定理，位于命名空间 `AffineBasis`。
形式化陈述：toMatrix_mul_toMatrix : b.toMatrix b₂ * b₂.toMatrix b = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineBasis.toMatrix_vecMul_coords`：toMatrix_vecMul_coords (x : P) : b₂.
coords x ᵥ* b.toMatrix b₂ = b.coords x
· 使用定理 `AffineBasis.coords_apply`：coords_apply (q : P) (i : ι) : b.coords q i = 
b.coord i q
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineBasis.toMatrix_apply`：toMatrix_apply {ι' : Type*} (q : ι' -> P) (i
 : ι') (j : ι) : b.toMatrix q i j = b.coord j (q i)
· 使用定理 `AffineBasis.toMatrix_self`：toMatrix_self [DecidableEq ι] : b.toMatrix b 
= (1 : Matrix ι ι k)
-/
theorem toMatrix_mul_toMatrix : b.toMatrix b₂ * b₂.toMatrix b = 1 := by
  ext l m
  change (b.coords (b₂ l) ᵥ* b₂.toMatrix b) m = _
  rw [toMatrix_vecMul_coords, coords_apply, ← toMatrix_apply, toMatrix_self]
/-
**AffineBasis.isUnit_toMatrix** 是 Mathlib 中的一个定理，位于命名空间 `AffineBasis`。
形式化陈述：isUnit_toMatrix : IsUnit (b.toMatrix b₂)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineBasis.toMatrix_mul_toMatrix`：toMatrix_mul_toMatrix : b.toMatrix b₂
 * b₂.toMatrix b = 1
-/
theorem isUnit_toMatrix : IsUnit (b.toMatrix b₂) :=
  ⟨{  val := b.toMatrix b₂
      inv := b₂.toMatrix b
      val_inv := b.toMatrix_mul_toMatrix b₂
      inv_val := b₂.toMatrix_mul_toMatrix b }, rfl⟩
/-
**AffineBasis.isUnit_toMatrix_iff** 是 Mathlib 中的一个定理，位于命名空间 `AffineBasis`。
形式化陈述：isUnit_toMatrix_iff [Nontrivial k] (p : ι -> P) : IsUnit (b.toMatrix p) ↔ 
AffineIndependent k p ∧ affineSpan k (range p) = ⊤
参数：p : ι -> P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineBasis.affineIndependent_of_toMatrix_right_inv`：affineIndependent_o
f_toMatrix_right_inv [Fintype ι] [Finite ι'] [DecidableEq ι'] (p : ι' -> P) {A :
 Matrix ι ι' k} (hA : b.toMatrix p * A = …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `AffineBasis.affineSpan_eq_top_of_toMatrix_left_inv`：affineSpan_eq_top_of
_toMatrix_left_inv [Finite ι] [Fintype ι'] [DecidableEq ι] [Nontrivial k] (p : ι
' -> P) {A : Matrix ι ι' k} (hA : A * b.…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineBasis.isUnit_toMatrix`：isUnit_toMatrix : IsUnit (b.toMatrix b₂)
-/
theorem isUnit_toMatrix_iff [Nontrivial k] (p : ι → P) :
    IsUnit (b.toMatrix p) ↔ AffineIndependent k p ∧ affineSpan k (range p) = ⊤ := by
  constructor
  · rintro ⟨⟨B, A, hA, hA'⟩, rfl : B = b.toMatrix p⟩
    exact ⟨b.affineIndependent_of_toMatrix_right_inv p hA,
      b.affineSpan_eq_top_of_toMatrix_left_inv p hA'⟩
  · rintro ⟨h_tot, h_ind⟩
    let b' : AffineBasis ι k P := ⟨p, h_tot, h_ind⟩
    change IsUnit (b.toMatrix b')
    exact b.isUnit_toMatrix b'

end Ring

section CommRing

variable [CommRing k] [Module k V] [DecidableEq ι] [Fintype ι]
variable (b b₂ : AffineBasis ι k P)

/-- A change of basis formula for barycentric coordinates.

See also `AffineBasis.toMatrix_vecMul_coords`. -/
@[simp]
/-
**AffineBasis.toMatrix_inv_vecMul_toMatrix** 是 Mathlib 中的一个定理，位于命名空间 `AffineBasi
s`。
形式化陈述：toMatrix_inv_vecMul_toMatrix (x : P) : b.coords x ᵥ* (b.toMatrix b₂)⁻¹ = b
₂.coords x
参数：x : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineBasis.isUnit_toMatrix`：isUnit_toMatrix : IsUnit (b.toMatrix b₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineBasis.toMatrix_vecMul_coords`：toMatrix_vecMul_coords (x : P) : b₂.
coords x ᵥ* b.toMatrix b₂ = b.coords x
· 使用定理 `Matrix.vecMul_vecMul`：vecMul_vecMul [Fintype n] [Fintype m] (v : m -> α)
 (M : Matrix m n α) (N : Matrix n o α) : v ᵥ* M ᵥ* N = v ᵥ* (M * N)
· 使用定理 `Matrix.mul_nonsing_inv`：mul_nonsing_inv (h : IsUnit A.det) : A * A⁻¹ = 1
· 使用定理 `Matrix.isUnit_iff_isUnit_det`：isUnit_iff_isUnit_det : IsUnit A ↔ IsUnit 
A.det
· 使用定理 `Matrix.vecMul_one`：vecMul_one (v : m -> α) : v ᵥ* 1 = v

--- 原说明 ---
A change of basis formula for barycentric coordinates.

See also `AffineBasis.toMatrix_vecMul_coords`.
-/
theorem toMatrix_inv_vecMul_toMatrix (x : P) :
    b.coords x ᵥ* (b.toMatrix b₂)⁻¹ = b₂.coords x := by
  have hu := b.isUnit_toMatrix b₂
  rw [Matrix.isUnit_iff_isUnit_det] at hu
  rw [← b.toMatrix_vecMul_coords b₂, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hu,
    Matrix.vecMul_one]

/-- If we fix a background affine basis `b`, then for any other basis `b₂`, we can characterise
the barycentric coordinates provided by `b₂` in terms of determinants relative to `b`. -/
/-
**AffineBasis.det_smul_coords_eq_cramer_coords** 是 Mathlib 中的一个定理，位于命名空间 `Affine
Basis`。
形式化陈述：det_smul_coords_eq_cramer_coords (x : P) : (b.toMatrix b₂).det • b₂.coords
 x = (b.toMatrix b₂)ᵀ.cramer (b.coords x)
参数：x : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineBasis.isUnit_toMatrix`：isUnit_toMatrix : IsUnit (b.toMatrix b₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineBasis.toMatrix_inv_vecMul_toMatrix`：toMatrix_inv_vecMul_toMatrix (
x : P) : b.coords x ᵥ* (b.toMatrix b₂)⁻¹ = b₂.coords x
· 使用定理 `Matrix.det_smul_inv_vecMul_eq_cramer_transpose`：det_smul_inv_vecMul_eq_c
ramer_transpose (A : Matrix n n α) (b : n -> α) (h : IsUnit A.det) : A.det • b ᵥ
* A⁻¹ = cramer Aᵀ b
· 使用定理 `Matrix.isUnit_iff_isUnit_det`：isUnit_iff_isUnit_det : IsUnit A ↔ IsUnit 
A.det

--- 原说明 ---
If we fix a background affine basis `b`, then for any other basis `b₂`, we can c
haracterise
the barycentric coordinates provided by `b₂` in terms of determinants relative t
o `b`.
-/
theorem det_smul_coords_eq_cramer_coords (x : P) :
    (b.toMatrix b₂).det • b₂.coords x = (b.toMatrix b₂)ᵀ.cramer (b.coords x) := by
  have hu := b.isUnit_toMatrix b₂
  rw [Matrix.isUnit_iff_isUnit_det] at hu
  rw [← b.toMatrix_inv_vecMul_toMatrix, Matrix.det_smul_inv_vecMul_eq_cramer_transpose _ _ hu]

end CommRing

end AffineBasis

