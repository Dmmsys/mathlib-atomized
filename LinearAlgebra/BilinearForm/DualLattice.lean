/-
Copyright (c) 2018 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!

# Dual submodule with respect to a bilinear form.

## Main definitions and results
- `BilinForm.dualSubmodule`: The dual submodule with respect to a bilinear form.
- `BilinForm.dualSubmodule_span_of_basis`: The dual of a lattice is spanned by the dual basis.

## TODO
Properly develop the material in the context of lattices.
-/

@[expose] public section

open LinearMap (BilinForm)
open Module

variable {R S M} [CommRing R] [Field S] [AddCommGroup M]
variable [Algebra R S] [Module R M] [Module S M] [IsScalarTower R S M]

namespace LinearMap

namespace BilinForm

variable (B : BilinForm S M)

/-- The dual submodule of a submodule with respect to a bilinear form. -/
/-
**LinearMap.BilinForm.dualSubmodule** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap.BilinFo
rm`。
形式化陈述：dualSubmodule (N : Submodule R M) : Submodule R M where carrier
参数：N : Submodule R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The dual submodule of a submodule with respect to a bilinear form.
-/
def dualSubmodule (N : Submodule R M) : Submodule R M where
  carrier := { x | ∀ y ∈ N, B x y ∈ (1 : Submodule R S) }
  add_mem' {a b} ha hb y hy := by simpa using add_mem (ha y hy) (hb y hy)
  zero_mem' y _ := by rw [B.zero_left]; exact zero_mem _
  smul_mem' r a ha y hy := by
    convert! (1 : Submodule R S).smul_mem r (ha y hy)
    rw [← IsScalarTower.algebraMap_smul S r a]
    simp only [algebraMap_smul, map_smul_of_tower, LinearMap.smul_apply]
/-
**LinearMap.BilinForm.mem_dualSubmodule** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap.Bil
inForm`。
形式化陈述：mem_dualSubmodule {N : Submodule R M} {x} : x in B.dualSubmodule N ↔ foral
l y in N, B x y in (1 : Submodule R S)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_dualSubmodule {N : Submodule R M} {x} :
    x ∈ B.dualSubmodule N ↔ ∀ y ∈ N, B x y ∈ (1 : Submodule R S) := Iff.rfl
/-
**LinearMap.BilinForm.le_flip_dualSubmodule** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap
.BilinForm`。
形式化陈述：le_flip_dualSubmodule {N₁ N₂ : Submodule R M} : N₁ <= B.flip.dualSubmodule
 N₂ ↔ N₂ <= B.dualSubmodule N₁
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall₂_comm`：forall₂_comm {ι₁ ι₂ : Sort*} {κ₁ : ι₁ -> Sort*} {κ₂ : ι₂ -
> Sort*} {p : forall i₁, κ₁ i₁ -> forall i₂, κ₂ i₂ -> Prop} : (forall i₁ j₁ i₂ j
₂,…
-/
lemma le_flip_dualSubmodule {N₁ N₂ : Submodule R M} :
    N₁ ≤ B.flip.dualSubmodule N₂ ↔ N₂ ≤ B.dualSubmodule N₁ := by
  change (∀ (x : M), x ∈ N₁ → _) ↔ ∀ (x : M), x ∈ N₂ → _
  simp only [mem_dualSubmodule, Submodule.mem_one, flip_apply]
  exact forall₂_comm

/-- The natural paring of `B.dualSubmodule N` and `N`.
This is bundled as a bilinear map in `BilinForm.dualSubmoduleToDual`. -/
noncomputable
/-
**LinearMap.BilinForm.dualSubmoduleParing** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap.B
ilinForm`。
形式化陈述：dualSubmoduleParing {N : Submodule R M} (x : B.dualSubmodule N) (y : N) : 
R
参数：x : B.dualSubmodule N；y : N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def dualSubmoduleParing {N : Submodule R M} (x : B.dualSubmodule N) (y : N) : R :=
  (Submodule.mem_one.mp <| x.prop y y.prop).choose

@[simp]
/-
**LinearMap.BilinForm.dualSubmoduleParing_spec** 是 Mathlib 中的一个引理，位于命名空间 `Linear
Map.BilinForm`。
形式化陈述：dualSubmoduleParing_spec {N : Submodule R M} (x : B.dualSubmodule N) (y : 
N) : algebraMap R S (B.dualSubmoduleParing x y) = B x y
参数：x : B.dualSubmodule N；y : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_one`：mem_one {x : A} : x in (1 : Submodule R A) ↔ exists y
, algebraMap R A y = x
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
lemma dualSubmoduleParing_spec {N : Submodule R M} (x : B.dualSubmodule N) (y : N) :
    algebraMap R S (B.dualSubmoduleParing x y) = B x y :=
  (Submodule.mem_one.mp <| x.prop y y.prop).choose_spec

/-- The natural paring of `B.dualSubmodule N` and `N`. -/
-- TODO: Show that this is perfect when `N` is a lattice and `B` is nondegenerate.
@[simps]
noncomputable
/-
**LinearMap.BilinForm.dualSubmoduleToDual** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap.B
ilinForm`。
形式化陈述：dualSubmoduleToDual [IsDomain R] [IsTorsionFree R S] (N : Submodule R M) :
 B.dualSubmodule N ->ₗ[R] Module.Dual R N
参数：N : Submodule R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def dualSubmoduleToDual [IsDomain R] [IsTorsionFree R S] (N : Submodule R M) :
    B.dualSubmodule N →ₗ[R] Module.Dual R N :=
  { toFun := fun x ↦
    { toFun := B.dualSubmoduleParing x
      map_add' := fun x y ↦ FaithfulSMul.algebraMap_injective R S (by simp)
      map_smul' := fun r m ↦ FaithfulSMul.algebraMap_injective R S
        (by simp [← Algebra.smul_def]) }
    map_add' := fun x y ↦ LinearMap.ext fun z ↦ FaithfulSMul.algebraMap_injective R S
      (by simp)
    map_smul' := fun r x ↦ LinearMap.ext fun y ↦ FaithfulSMul.algebraMap_injective R S
      (by simp [← Algebra.smul_def]) }
/-
**LinearMap.BilinForm.dualSubmoduleToDual_injective** 是 Mathlib 中的一个引理，位于命名空间 `L
inearMap.BilinForm`。
形式化陈述：dualSubmoduleToDual_injective [IsDomain R] (hB : B.Nondegenerate) [IsTorsi
onFree R S] (N : Submodule R M) (hN : Submodule.span S (N : Set M) = ⊤) : Functi
on.Injective (B.dualSubmoduleToDual N)
参数：hB : B.Nondegenerate；N : Submodule R M；hN : Submodule.span S (N : Set M) = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `LinearMap.BilinForm.Nondegenerate.ker_eq_bot`：∀ {R : Type u_1} {M : Type
 u_2} [inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module
 R M]   {B : LinearMap.BilinForm R…
· 使用定理 `LinearMap.ext_on`：ext_on {s : Set M} {f g : M ->ₛₗ[σ₁₂] M₂} (hv : span R
 s = ⊤) (h : Set.EqOn f g s) : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.BilinForm.dualSubmoduleToDual_apply_apply`：∀ {R : Type u_1} {S
 : Type u_2} {M : Type u_3} [inst : CommRing R] [inst_1 : Field S] [inst_2 : Add
CommGroup M]   [inst_3 : Algebra R S] [in…
· 使用引理 `LinearMap.BilinForm.dualSubmoduleParing_spec`：dualSubmoduleParing_spec {
N : Submodule R M} (x : B.dualSubmodule N) (y : N) : algebraMap R S (B.dualSubmo
duleParing x y) = B x y
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
-/
lemma dualSubmoduleToDual_injective [IsDomain R] (hB : B.Nondegenerate) [IsTorsionFree R S]
    (N : Submodule R M) (hN : Submodule.span S (N : Set M) = ⊤) :
    Function.Injective (B.dualSubmoduleToDual N) := by
  intro x y e
  ext
  apply LinearMap.ker_eq_bot.mp hB.ker_eq_bot
  apply LinearMap.ext_on hN
  intro z hz
  simpa using congr_arg (algebraMap R S) (LinearMap.congr_fun e ⟨z, hz⟩)
/-
**LinearMap.BilinForm.dualSubmodule_span_of_basis** 是 Mathlib 中的一个引理，位于命名空间 `Lin
earMap.BilinForm`。
形式化陈述：dualSubmodule_span_of_basis {ι} [Finite ι] [DecidableEq ι] (hB : B.Nondege
nerate) (b : Basis ι S M) : B.dualSubmodule (Submodule.span R (Set.range b)) = S
ubmodule.span R (Set.range <| B.dualBasis hB b)
参数：hB : B.Nondegenerate；b : Basis ι S M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.sum_repr`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} [i
nst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [ins
t_3 : Finty…
· 使用定理 `sum_mem`：∀ {B : Type u_3} {S : B} {M : Type u_4} [inst : AddCommMonoid M
] [inst_1 : SetLike B M] [AddSubmonoidClass B M]   {ι : Type u_5} {t : Finset…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_one`：mem_one {x : A} : x in (1 : Submodule R A) ↔ exists y
, algebraMap R A y = x
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.BilinForm.dualBasis_repr_apply`：dualBasis_repr_apply (hB : B.N
ondegenerate) (b : Basis ι K V) (x i) : (B.dualBasis hB b).repr x i = B x (b i)
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Submodule.mem_span_range_iff_exists_fun`：Submodule.mem_span_range_iff_ex
ists_fun : x in span R (range v) ↔ exists c : α -> R, ∑ i, c i • v i = x
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `IsScalarTower.algebraMap_smul`：algebraMap_smul [SMul R M] [IsScalarTower
 R A M] (r : R) (x : M) : algebraMap R A r • x = r • x
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `LinearMap.BilinForm.apply_dualBasis_left`：apply_dualBasis_left (hB : B.N
ondegenerate) (b : Basis ι K V) (i j) : B (B.dualBasis hB b i) (b j) = if j = i 
then 1 else 0
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `RingHom.map_zero`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring 
α} {x_1 : NonAssocSemiring β} (f : α →+* β), f 0 = 0
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
lemma dualSubmodule_span_of_basis {ι} [Finite ι] [DecidableEq ι]
    (hB : B.Nondegenerate) (b : Basis ι S M) :
    B.dualSubmodule (Submodule.span R (Set.range b)) =
      Submodule.span R (Set.range <| B.dualBasis hB b) := by
  cases nonempty_fintype ι
  apply le_antisymm
  · intro x hx
    rw [← (B.dualBasis hB b).sum_repr x]
    apply sum_mem
    rintro i -
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp <| hx (b i) (Submodule.subset_span ⟨_, rfl⟩)
    simp only [dualBasis_repr_apply, ← hr, algebraMap_smul]
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨_, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩ y hy
    obtain ⟨f, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hy
    simp only [map_sum]
    apply sum_mem
    rintro j -
    rw [← IsScalarTower.algebraMap_smul S (f j), map_smul]
    simp_rw [apply_dualBasis_left]
    rw [smul_eq_mul, mul_ite, mul_one, mul_zero, ← (algebraMap R S).map_zero, ← apply_ite]
    exact Submodule.mem_one.mpr ⟨_, rfl⟩
/-
**LinearMap.BilinForm.dualSubmodule_dualSubmodule_flip_of_basis** 是 Mathlib 中的一个
引理，位于命名空间 `LinearMap.BilinForm`。
形式化陈述：dualSubmodule_dualSubmodule_flip_of_basis {ι : Type*} [Finite ι] (hB : B.N
ondegenerate) (b : Basis ι S M) : B.dualSubmodule (B.flip.dualSubmodule (Submodu
le.span R (Set.range b))) = Submodule.span R (Set.range b)
参数：hB : B.Nondegenerate；b : Basis ι S M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.finiteDimensional_of_finite`：∀ {K : Type u} {V : Type v} [i
nst : DivisionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V] {ι 
: Type w}   [Finite ι] (h : Mo…
· 使用定理 `LinearMap.BilinForm.Nondegenerate.flip`：∀ {R : Type u_1} {M : Type u_2} 
[inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] 
  {B : LinearMap.BilinForm R…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearMap.BilinForm.dualSubmodule_span_of_basis`：dualSubmodule_span_of_b
asis {ι} [Finite ι] [DecidableEq ι] (hB : B.Nondegenerate) (b : Basis ι S M) : B
.dualSubmodule (Submodule.span R (Set…
· 使用引理 `LinearMap.BilinForm.dualBasis_dualBasis_flip`：dualBasis_dualBasis_flip (
hB : B.Nondegenerate) (b : Basis ι K V) : B.dualBasis hB (B.flip.dualBasis hB.fl
ip b) = b
-/
lemma dualSubmodule_dualSubmodule_flip_of_basis {ι : Type*} [Finite ι]
    (hB : B.Nondegenerate) (b : Basis ι S M) :
    B.dualSubmodule (B.flip.dualSubmodule (Submodule.span R (Set.range b))) =
      Submodule.span R (Set.range b) := by
  classical
  let := b.finiteDimensional_of_finite
  rw [dualSubmodule_span_of_basis _ hB.flip, dualSubmodule_span_of_basis B hB,
    dualBasis_dualBasis_flip hB]
/-
**LinearMap.BilinForm.dualSubmodule_flip_dualSubmodule_of_basis** 是 Mathlib 中的一个
引理，位于命名空间 `LinearMap.BilinForm`。
形式化陈述：dualSubmodule_flip_dualSubmodule_of_basis {ι : Type*} [Finite ι] (hB : B.N
ondegenerate) (b : Basis ι S M) : B.flip.dualSubmodule (B.dualSubmodule (Submodu
le.span R (Set.range b))) = Submodule.span R (Set.range b)
参数：hB : B.Nondegenerate；b : Basis ι S M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.finiteDimensional_of_finite`：∀ {K : Type u} {V : Type v} [i
nst : DivisionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V] {ι 
: Type w}   [Finite ι] (h : Mo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearMap.BilinForm.dualSubmodule_span_of_basis`：dualSubmodule_span_of_b
asis {ι} [Finite ι] [DecidableEq ι] (hB : B.Nondegenerate) (b : Basis ι S M) : B
.dualSubmodule (Submodule.span R (Set…
· 使用定理 `LinearMap.BilinForm.Nondegenerate.flip`：∀ {R : Type u_1} {M : Type u_2} 
[inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] 
  {B : LinearMap.BilinForm R…
· 使用引理 `LinearMap.BilinForm.dualBasis_flip_dualBasis`：dualBasis_flip_dualBasis (
hB : B.Nondegenerate) (b : Basis ι K V) : B.flip.dualBasis hB.flip (B.dualBasis 
hB b) = b
-/
lemma dualSubmodule_flip_dualSubmodule_of_basis {ι : Type*} [Finite ι]
    (hB : B.Nondegenerate) (b : Basis ι S M) :
    B.flip.dualSubmodule (B.dualSubmodule (Submodule.span R (Set.range b))) =
      Submodule.span R (Set.range b) := by
  classical
  let := b.finiteDimensional_of_finite
  rw [dualSubmodule_span_of_basis B hB, dualSubmodule_span_of_basis _ hB.flip,
    dualBasis_flip_dualBasis hB]
/-
**LinearMap.BilinForm.dualSubmodule_dualSubmodule_of_basis** 是 Mathlib 中的一个引理，位于
命名空间 `LinearMap.BilinForm`。
形式化陈述：dualSubmodule_dualSubmodule_of_basis {ι} [Finite ι] (hB : B.Nondegenerate)
 (hB' : B.IsSymm) (b : Basis ι S M) : B.dualSubmodule (B.dualSubmodule (Submodul
e.span R (Set.range b))) = Submodule.span R (Set.range b)
参数：hB : B.Nondegenerate；hB' : B.IsSymm；b : Basis ι S M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.finiteDimensional_of_finite`：∀ {K : Type u} {V : Type v} [i
nst : DivisionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V] {ι 
: Type w}   [Finite ι] (h : Mo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearMap.BilinForm.dualSubmodule_span_of_basis`：dualSubmodule_span_of_b
asis {ι} [Finite ι] [DecidableEq ι] (hB : B.Nondegenerate) (b : Basis ι S M) : B
.dualSubmodule (Submodule.span R (Set…
· 使用引理 `LinearMap.BilinForm.dualBasis_dualBasis`：dualBasis_dualBasis (hB : B.Non
degenerate) (hB' : B.IsSymm) (b : Basis ι K V) : B.dualBasis hB (B.dualBasis hB 
b) = b
-/
lemma dualSubmodule_dualSubmodule_of_basis
    {ι} [Finite ι] (hB : B.Nondegenerate) (hB' : B.IsSymm) (b : Basis ι S M) :
    B.dualSubmodule (B.dualSubmodule (Submodule.span R (Set.range b))) =
      Submodule.span R (Set.range b) := by
  classical
  let := b.finiteDimensional_of_finite
  rw [dualSubmodule_span_of_basis B hB, dualSubmodule_span_of_basis B hB,
    dualBasis_dualBasis hB hB']

end BilinForm

end LinearMap

