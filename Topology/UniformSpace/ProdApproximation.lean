/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Indicator
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.Separation.DisjointCover

/-!
# Uniform approximation by products

We show that if `X, Y` are compact Hausdorff spaces with `X` profinite, then any continuous function
on `X × Y` valued in a ring (with a uniform structure) can be uniformly approximated by finite
sums of functions of the form `f x * g y`.
-/

public section

open UniformSpace

open scoped Uniformity

namespace ContinuousMap

variable {X Y R V : Type*}
  [TopologicalSpace X] [TotallyDisconnectedSpace X] [T2Space X] [CompactSpace X]
  [TopologicalSpace Y] [CompactSpace Y]
  [AddCommGroup V] [UniformSpace V] [IsUniformAddGroup V] {S : Set (V × V)}

/-- A continuous function on `X × Y`, taking values in an `R`-module with a uniform structure,
can be uniformly approximated by sums of functions of the form `(x, y) ↦ f x • g y`.

Note that no continuity properties are assumed either for multiplication on `R`, or for the scalar
multiplication of `R` on `V`. -/
/-
**ContinuousMap.exists_finite_sum_smul_approximation_of_mem_uniformity** 是 Mathl
ib 中的一个引理，位于命名空间 `ContinuousMap`。
形式化陈述：exists_finite_sum_smul_approximation_of_mem_uniformity [TopologicalSpace R
] [MonoidWithZero R] [MulActionWithZero R V] (f : C(X × Y, V)) (hS : S in 𝓤 V) :
 exists (n : Nat) (g : Fin n -> C(X, R)) (h : Fin n -> C(Y, V)), forall x y, (f 
(x, y), ∑ i, g i x • h i y) in S
参数：f : C(X × Y, V)；hS : S in 𝓤 V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ContinuousMap.mem_compactConvergence_entourage_iff`：mem_compactConvergen
ce_entourage_iff (X : Set (C(α, β) × C(α, β))) : X in 𝓤 C(α, β) ↔ exists (K : Se
t α) (V : Set (β × β)), IsCompact K ∧ V …
· 使用定理 `isCompact_univ`：isCompact_univ [h : CompactSpace X] : IsCompact (univ : 
Set X)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_implies`：∀ (p : Prop), (True → p) = p
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsUniformAddGroup.to_topologicalAddGroup`：∀ {α : Type u_1} [inst : Unifo
rmSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α], IsTopologicalAddGroup α
· 使用定理 `ContinuousMap.exists_finite_sum_const_indicator_approximation_of_mem_nhd
s_diagonal`：∀ {X : Type u_1} {V : Type u_2} [inst : TopologicalSpace X] [inst_1 
: TopologicalSpace V] [TotallyDisconnectedSpace X]   [T2Space X] [Compac…
· 使用定理 `nhdsSet_diagonal_le_uniformity`：nhdsSet_diagonal_le_uniformity : 𝓝ˢ (dia
gonal α) <= 𝓤 α
· 使用定理 `IsClopen.continuous_indicator`：∀ {α : Type u_1} {β : Type u_2} [inst : T
opologicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α}   [inst
_2 : Zero β], IsClo…
· 使用定理 `TopologicalSpace.Clopens.isClopen`：isClopen (s : Clopens α) : IsClopen (
s : Set α)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `ContinuousMap.sum_apply`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolog
icalSpace α] [inst_1 : TopologicalSpace β] [inst_2 : AddCommMonoid β]   [inst_3 
: ContinuousA…
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
A continuous function on `X × Y`, taking values in an `R`-module with a uniform 
structure,
can be uniformly approximated by sums of functions of the form `(x, y) ↦ f x • g
 y`.

Note that no continuity properties are assumed either for multiplication on `R`,
 or for the scalar
multiplication of `R` on `V`.
-/
lemma exists_finite_sum_smul_approximation_of_mem_uniformity [TopologicalSpace R]
    [MonoidWithZero R] [MulActionWithZero R V] (f : C(X × Y, V)) (hS : S ∈ 𝓤 V) :
    ∃ (n : ℕ) (g : Fin n → C(X, R)) (h : Fin n → C(Y, V)),
    ∀ x y, (f (x, y), ∑ i, g i x • h i y) ∈ S := by
  have hS' : {(f, g) | ∀ y, (f y, g y) ∈ S} ∈ 𝓤 C(Y, V) :=
    (mem_compactConvergence_entourage_iff _).mpr
      ⟨_, _, isCompact_univ, hS, by simp only [Set.mem_univ, true_implies, subset_refl]⟩
  obtain ⟨n, U, v, hv⟩ := exists_finite_sum_const_indicator_approximation_of_mem_nhds_diagonal
    f.curry (nhdsSet_diagonal_le_uniformity hS')
  refine ⟨n, fun i ↦ ⟨_, (U i).isClopen.continuous_indicator <| continuous_const (y := 1)⟩,
    v, fun x y ↦ ?_⟩
  convert! hv x y using 2
  simp only [sum_apply]
  congr 1 with i
  by_cases hi : x ∈ U i <;> simp [hi]

/-- A continuous function on `X × Y`, taking values in a ring `R` equipped with a uniformity
compatible with addition, can be uniformly approximated by sums of functions of the form
`(x, y) ↦ f x * g y`.

Note that no assumption is needed relating the multiplication on `R` to the uniformity. -/
/-
**ContinuousMap.exists_finite_sum_mul_approximation_of_mem_uniformity** 是 Mathli
b 中的一个引理，位于命名空间 `ContinuousMap`。
形式化陈述：exists_finite_sum_mul_approximation_of_mem_uniformity [Ring R] [UniformSpa
ce R] [IsUniformAddGroup R] (f : C(X × Y, R)) {S : Set (R × R)} (hS : S in 𝓤 R) 
: exists (n : Nat) (g : Fin n -> C(X, R)) (h : Fin n -> C(Y, R)), forall x y, (f
 (x, y), ∑ i, g i x * h i y) in S
参数：f : C(X × Y, R)；R × R；hS : S in 𝓤 R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousMap.exists_finite_sum_smul_approximation_of_mem_uniformity`：ex
ists_finite_sum_smul_approximation_of_mem_uniformity [TopologicalSpace R] [Monoi
dWithZero R] [MulActionWithZero R V] (f : C(X × Y, V)) (hS…

--- 原说明 ---
A continuous function on `X × Y`, taking values in a ring `R` equipped with a un
iformity
compatible with addition, can be uniformly approximated by sums of functions of 
the form
`(x, y) ↦ f x * g y`.

Note that no assumption is needed relating the multiplication on `R` to the unif
ormity.
-/
lemma exists_finite_sum_mul_approximation_of_mem_uniformity [Ring R] [UniformSpace R]
    [IsUniformAddGroup R] (f : C(X × Y, R)) {S : Set (R × R)} (hS : S ∈ 𝓤 R) :
    ∃ (n : ℕ) (g : Fin n → C(X, R)) (h : Fin n → C(Y, R)),
    ∀ x y, (f (x, y), ∑ i, g i x * h i y) ∈ S :=
  exists_finite_sum_smul_approximation_of_mem_uniformity f hS

section prodMul

open scoped TensorProduct

variable {X Y R : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

/-- The natural bilinear map sending `f, g` to the function `(x, y) ↦ f x * g y` on `X × Y`. -/
/-
**ContinuousMap.prodMul** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：prodMul : C(X, R) ->ₗ[R] C(Y, R) ->ₗ[R] C(X × Y, R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural bilinear map sending `f, g` to the function `(x, y) ↦ f x * g y` on 
`X × Y`.
-/
def prodMul : C(X, R) →ₗ[R] C(Y, R) →ₗ[R] C(X × Y, R) :=
  LinearMap.mk₂ R (fun f g ↦ (f.comp .fst) * (g.comp .snd))
    (fun f f' g ↦ by ext; simp [add_mul])
    (fun r f g ↦ by ext; simp)
    (fun f g g' ↦ by ext; simp [mul_add])
    (fun r f g ↦ by ext; simp)
/-
**ContinuousMap.prodMul_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：∀ {X : Type u_5} {Y : Type u_6} {R : Type u_7} [inst : TopologicalSpace X]
 [inst_1 : TopologicalSpace Y]   [inst_2 : CommRing R] [inst_3 : TopologicalSpac
e R] [inst_4 : IsTopologicalRing R] (f : C(X, R)) (g : C(Y, R))   (p : X × Y), (
(ContinuousMap.prodMul f) g) p = f p.1 * g p.2
参数：f : C(X, R)；g : C(Y, R)；p : X × Y；(ContinuousMap.prodMul f) g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `ContinuousMap.instSMulCommClass`：∀ {α : Type u_1} [inst : TopologicalSpa
ce α] {R : Type u_3} {R₁ : Type u_4} {M : Type u_5} [inst_1 : TopologicalSpace M
]   [inst_2 : SMul R …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
@[simp] lemma prodMul_apply (f : C(X, R)) (g : C(Y, R)) (p : X × Y) :
    f.prodMul g p  = f p.1 * g p.2 :=
  (rfl)
/-
**ContinuousMap.prodMul_def** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMap`。
形式化陈述：prodMul_def (f : C(X, R)) (g : C(Y, R)) : f.prodMul g = f.comp .fst * g.co
mp .snd
参数：f : C(X, R)；g : C(Y, R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `ContinuousMap.instSMulCommClass`：∀ {α : Type u_1} [inst : TopologicalSpa
ce α] {R : Type u_3} {R₁ : Type u_4} {M : Type u_5} [inst_1 : TopologicalSpace M
]   [inst_2 : SMul R …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
lemma prodMul_def (f : C(X, R)) (g : C(Y, R)) :
    f.prodMul g  = f.comp .fst * g.comp .snd :=
  (rfl)

/-- Tensor product version of `ContinuousMap.prodMul`. -/
/-
**ContinuousMap.tensorHom** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：tensorHom : C(X, R) otimes[R] C(Y, R) ->ₗ[R] C(X × Y, R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Tensor product version of `ContinuousMap.prodMul`.
-/
def tensorHom : C(X, R) ⊗[R] C(Y, R) →ₗ[R] C(X × Y, R) :=
  TensorProduct.lift prodMul

@[simp]
/-
**ContinuousMap.tensorHom_tmul** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMap`。
形式化陈述：tensorHom_tmul (f : C(X, R)) (g : C(Y, R)) : tensorHom (f otimesₜ g) = pro
dMul f g
参数：f : C(X, R)；g : C(Y, R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `ContinuousMap.instSMulCommClass`：∀ {α : Type u_1} [inst : TopologicalSpa
ce α] {R : Type u_3} {R₁ : Type u_4} {M : Type u_5} [inst_1 : TopologicalSpace M
]   [inst_2 : SMul R …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Topology.UniformSpace.ProdApproximation.0.ContinuousMap
.tensorHom.eq_1`：∀ {X : Type u_5} {Y : Type u_6} {R : Type u_7} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : CommRing R] [inst_3 : T…
· 使用定理 `TensorProduct.lift.tmul`：∀ {R : Type u_1} {R₂ : Type u_2} [inst : CommSe
miring R] [inst_1 : CommSemiring R₂] {σ₁₂ : R →+* R₂} {M : Type u_7}   {N : Type
 u_8} {P₂ : T…
-/
lemma tensorHom_tmul (f : C(X, R)) (g : C(Y, R)) :
    tensorHom (f ⊗ₜ g) = prodMul f g := by
  rw [tensorHom, TensorProduct.lift.tmul]
/-
**ContinuousMap.denseRange_tensorHom** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMap`。
形式化陈述：denseRange_tensorHom [CompactSpace X] [T2Space X] [CompactSpace Y] [Totall
yDisconnectedSpace X] : DenseRange (tensorHom : C(X, R) otimes[R] C(Y, R) -> C(X
 × Y, R))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalRing.toIsTopologicalAddGroup`：∀ {R : Type u_1} [inst : 
NonUnitalNonAssocRing R] [inst_1 : TopologicalSpace R] [IsSemitopologicalRing R]
,   IsTopologicalAddGroup R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `isUniformAddGroup_of_addCommGroup`：∀ {G : Type u_1} [inst : AddCommGroup
 G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGroup G],   IsUnifor
mAddGroup G
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhds_uniformity_iff_right`：mem_nhds_uniformity_iff_right {x : α} {s 
: Set α} : s in 𝓝 x ↔ { p : α × α | p.1 = x -> p.2 in s } in 𝓤 α
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `ContinuousMap.hasBasis_compactConvergenceUniformity_of_compact`：hasBasis
_compactConvergenceUniformity_of_compact : HasBasis (𝓤 C(α, β)) (fun V : Set (β 
× β) => V in 𝓤 β) fun V => {fg : C(α, β) × C(α, β) |…
· 使用定理 `instCompactSpaceProd`：∀ {X : Type u} {Y : Type v} [inst : TopologicalSpa
ce X] [inst_1 : TopologicalSpace Y] [CompactSpace X] [CompactSpace Y],   Compact
Space (X ×…
· 使用引理 `ContinuousMap.exists_finite_sum_mul_approximation_of_mem_uniformity`：exi
sts_finite_sum_mul_approximation_of_mem_uniformity [Ring R] [UniformSpace R] [Is
UniformAddGroup R] (f : C(X × Y, R)) {S : Set (R × R)} (h…
· 使用定理 `Set.mem_of_subset_of_mem`：∀ {α : Type u} {s₁ s₂ : Set α} {a : α}, s₁ ⊆ s
₂ → a ∈ s₁ → a ∈ s₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
（共 35 条，此处仅展示前 30 条）
-/
lemma denseRange_tensorHom [CompactSpace X] [T2Space X] [CompactSpace Y]
    [TotallyDisconnectedSpace X] : DenseRange (tensorHom : C(X, R) ⊗[R] C(Y, R) → C(X × Y, R)) := by
  let : UniformSpace R := IsTopologicalAddGroup.rightUniformSpace R
  let : IsUniformAddGroup R := isUniformAddGroup_of_addCommGroup
  intro f
  simp_rw [mem_closure_iff, Set.nonempty_def]
  intro U hUo hUf
  have := mem_nhds_uniformity_iff_right.mp (hUo.mem_nhds hUf)
  obtain ⟨J, hJu, hJ'⟩ := (hasBasis_compactConvergenceUniformity_of_compact).mem_iff.mp this
  obtain ⟨n, g, h, hgh⟩ := exists_finite_sum_mul_approximation_of_mem_uniformity f hJu
  have hG := Set.mem_of_subset_of_mem hJ' (a := (f, tensorHom <| ∑ i, g i ⊗ₜ h i))
  simp only [Prod.forall, Set.mem_ofPred_eq, forall_const] at hG
  simpa using ⟨_, hG <| by simpa [tensorHom] using hgh⟩

end prodMul

end ContinuousMap

