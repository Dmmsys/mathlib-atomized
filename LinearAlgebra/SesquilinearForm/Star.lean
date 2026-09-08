/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Sesquilinear forms over a star ring

This file provides some properties about sesquilinear forms `M →ₗ⋆[R] M →ₗ[R] R` when `R` is a
`StarRing`.
-/

public section

open Module LinearMap

variable {R M n : Type*} [CommSemiring R] [StarRing R] [AddCommMonoid M] [Module R M]
  [Fintype n] [DecidableEq n]
  {B : M →ₗ⋆[R] M →ₗ[R] R} (b : Basis n R M)

set_option backward.isDefEq.respectTransparency false in
/-
**LinearMap.isSymm_iff_basis** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearMap.isSymm_iff_basis {ι : Type*} (b : Basis ι R M) : IsSymm B ↔ fora
ll i j, star (B (b i) (b j)) = B (b j) (b i) where mp h i j
参数：b : Basis ι R M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.IsSymm.eq`：∀ {R : Type u_1} {M : Type u_5} [inst : CommSemirin
g R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {I : R →+* R} {B 
: M →ₛₗ[I…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Submodule.mem_span_iff_exists_finset_subset`：Submodule.mem_span_iff_exis
ts_finset_subset {s : Set M} {x : M} : x in span R s ↔ exists (f : M -> R) (t : 
Finset M), ↑t subseteq s ∧ f.supp…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.span_eq`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b : 
Module.Bas…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `LinearMap.map_smulₛₗ`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃
 : Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearMap.coe_sum`：coe_sum {ι : Type*} (t : Finset ι) (f : ι -> M ->ₛₗ[σ
₁₂] M₂) : ⇑(∑ i in t, f i) = ∑ i in t, (f i : M -> M₂)
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `Finset.sum_comm`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst : 
AddCommMonoid β] {s : Finset γ} {t : Finset α} {f : γ → α → β},   ∑ x ∈ s, ∑ y ∈
 t, f…
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
-/
lemma LinearMap.isSymm_iff_basis {ι : Type*} (b : Basis ι R M) :
    IsSymm B ↔ ∀ i j, star (B (b i) (b j)) = B (b j) (b i) where
  mp h i j := h.eq _ _
  mpr := by
    refine fun h ↦ ⟨fun x y ↦ ?_⟩
    obtain ⟨fx, tx, ix, -, hx⟩ := Submodule.mem_span_iff_exists_finset_subset.1
      (by simp : x ∈ Submodule.span R (Set.range b))
    obtain ⟨fy, ty, iy, -, hy⟩ := Submodule.mem_span_iff_exists_finset_subset.1
      (by simp : y ∈ Submodule.span R (Set.range b))
    rw [← hx, ← hy]
    simp only [map_sum, LinearMap.map_smulₛₗ, starRingEnd_apply, map_smul, coe_sum,
      Finset.sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum, map_mul, star_star]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b₁ h₁ ↦ Finset.sum_congr rfl fun b₂ h₂ ↦ ?_)
    rw [mul_left_comm]
    obtain ⟨i, rfl⟩ := ix h₁
    obtain ⟨j, rfl⟩ := iy h₂
    rw [h]
/-
**LinearMap.isSymm_iff_isHermitian_toMatrix** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearMap.isSymm_iff_isHermitian_toMatrix : B.IsSymm ↔ (toMatrix₂ b b B).I
sHermitian
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearMap.isSymm_iff_basis`：LinearMap.isSymm_iff_basis {ι : Type*} (b : 
Basis ι R M) : IsSymm B ↔ forall i j, star (B (b i) (b j)) = B (b j) (b i) where
 mp h i j
· 使用定理 `Matrix.IsHermitian.ext_iff`：∀ {α : Type u_1} {n : Type u_4} [inst : Star
 α] {A : Matrix n n α}, A.IsHermitian ↔ ∀ (i j : n), star (A j i) = A i j
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `LinearMap.toMatrix₂_apply`：LinearMap.toMatrix₂_apply (B : M₁ ->ₛₗ[σ₁] M₂
 ->ₛₗ[σ₂] N₂) (i : n) (j : m) : LinearMap.toMatrix₂ b₁ b₂ B i j = B (b₁ i) (b₂ j
)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma LinearMap.isSymm_iff_isHermitian_toMatrix : B.IsSymm ↔ (toMatrix₂ b b B).IsHermitian := by
  rw [isSymm_iff_basis b, Matrix.IsHermitian.ext_iff, forall_comm]
  simp [Eq.comm]
/-
**star_dotProduct_toMatrix** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma star_dotProduct_toMatrix₂_mulVec (x y : n → R) :
    star x ⬝ᵥ (toMatrix₂ b b B).mulVec y = B (b.equivFun.symm x) (b.equivFun.symm y) :=
  dotProduct_toMatrix₂_mulVec b b B x y
/-
**apply_eq_star_dotProduct_toMatrix** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma apply_eq_star_dotProduct_toMatrix₂_mulVec (x y : M) :
    B x y = star (b.repr x) ⬝ᵥ (toMatrix₂ b b B).mulVec (b.repr y) :=
  apply_eq_dotProduct_toMatrix₂_mulVec b b B x y

variable {R : Type*} [CommRing R] [StarRing R] [PartialOrder R] [Module R M]
  {B : M →ₗ⋆[R] M →ₗ[R] R} (b : Basis n R M)
/-
**LinearMap.isPosSemidef_iff_posSemidef_toMatrix** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearMap.isPosSemidef_iff_posSemidef_toMatrix : B.IsPosSemidef ↔ (toMatri
x₂ b b B).PosSemidef
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearMap.isPosSemidef_def`：isPosSemidef_def [LE R] {B : M ->ₛₗ[I₁] M ->
ₗ[R] R} : B.IsPosSemidef ↔ B.IsSymm ∧ B.IsNonneg
· 使用定理 `Matrix.posSemidef_iff_dotProduct_mulVec`：posSemidef_iff_dotProduct_mulVe
c {M : Matrix n n R} : M.PosSemidef ↔ M.IsHermitian ∧ forall x, 0 <= star x ⬝ᵥ (
M *ᵥ x)
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用引理 `LinearMap.isSymm_iff_isHermitian_toMatrix`：LinearMap.isSymm_iff_isHermit
ian_toMatrix : B.IsSymm ↔ (toMatrix₂ b b B).IsHermitian
· 使用引理 `LinearMap.isNonneg_def`：isNonneg_def [LE R] {B : M ->ₛₗ[I₁] M ->ₛₗ[I₂] R
} : B.IsNonneg ↔ forall x, 0 <= B x x
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `star_dotProduct_toMatrix₂_mulVec`：star_dotProduct_toMatrix₂_mulVec (x y 
: n -> R) : star x ⬝ᵥ (toMatrix₂ b b B).mulVec y = B (b.equivFun.symm x) (b.equi
vFun.symm y)
· 使用引理 `apply_eq_star_dotProduct_toMatrix₂_mulVec`：apply_eq_star_dotProduct_toMa
trix₂_mulVec (x y : M) : B x y = star (b.repr x) ⬝ᵥ (toMatrix₂ b b B).mulVec (b.
repr y)
-/
lemma LinearMap.isPosSemidef_iff_posSemidef_toMatrix :
    B.IsPosSemidef ↔ (toMatrix₂ b b B).PosSemidef := by
  rw [isPosSemidef_def, Matrix.posSemidef_iff_dotProduct_mulVec]
  apply and_congr (B.isSymm_iff_isHermitian_toMatrix b)
  rw [isNonneg_def]
  refine ⟨fun h x ↦ ?_, fun h x ↦ ?_⟩
  · rw [star_dotProduct_toMatrix₂_mulVec]
    exact h _
  · rw [apply_eq_star_dotProduct_toMatrix₂_mulVec b]
    exact h _
