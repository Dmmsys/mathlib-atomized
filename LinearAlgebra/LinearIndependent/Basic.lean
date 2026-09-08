/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Alexander Bentkamp, Anne Baanen
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Linear independence

This file collects basic consequences of linear (in)dependence and includes specialized tests for
specific families of vectors.

## Main statements

We prove several specialized tests for linear independence of families of vectors and of sets of
vectors.

* `linearIndependent_empty_type`: a family indexed by an empty type is linearly independent;
* `linearIndependent_unique_iff`: if `ι` is a singleton, then `LinearIndependent K v` is
  equivalent to `v default ≠ 0`;
* `linearIndependent_sum`: type-specific test for linear independence of families of vector
  fields;
* `linearIndependent_singleton`: linear independence tests for set operations.

In many cases we additionally provide dot-style operations (e.g., `LinearIndependent.union`) to
make the linear independence tests usable as `hv.insert ha` etc.

## TODO

Rework proofs to hold in semirings, by avoiding the path through
`ker (Finsupp.linearCombination R v) = ⊥`.

## Tags

linearly dependent, linear dependence, linearly independent, linear independence

-/

public section

assert_not_exists Cardinal

noncomputable section

open Function Set Submodule

universe u' u

variable {ι : Type u'} {ι' : Type*} {R : Type*} {K : Type*} {s : Set ι}
variable {M : Type*} {M' : Type*} {V : Type u}

section Semiring


variable {v : ι → M}
variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M']
variable [Module R M] [Module R M']
variable (R) (v)

variable {R v}

/-- A set of linearly independent vectors in a module `M` over a semiring `K` is also linearly
independent over a subring `R` of `K`.

See also `LinearIndependent.restrict_scalars'` for a version with more convenient typeclass
assumptions.

TODO : `LinearIndepOn` version. -/
/-
**LinearIndependent.restrict_scalars** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.restrict_scalars [Semiring K] [SMulWithZero R K] [Module
 K M] [IsScalarTower R K M] (hinj : Injective fun r : R => r • (1 : K)) (li : Li
nearIndependent K v) : LinearIndependent R v
参数：hinj : Injective fun r : R => r • (1 : K)；li : LinearIndependent K v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finsupp.sum_mapRange_index`：∀ {α : Type u_1} {M : Type u_8} {M' : Type u
_9} {N : Type u_10} [inst : Zero M] [inst_1 : Zero M']   [inst_2 : AddCommMonoid
 N] {f : M → M'}…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g

--- 原说明 ---
A set of linearly independent vectors in a module `M` over a semiring `K` is als
o linearly
independent over a subring `R` of `K`.

See also `LinearIndependent.restrict_scalars'` for a version with more convenien
t typeclass
assumptions.

TODO : `LinearIndepOn` version.
-/
theorem LinearIndependent.restrict_scalars [Semiring K] [SMulWithZero R K] [Module K M]
    [IsScalarTower R K M] (hinj : Injective fun r : R ↦ r • (1 : K))
    (li : LinearIndependent K v) : LinearIndependent R v := by
  intro x y hxy
  let f := fun r : R => r • (1 : K)
  have := @li (x.mapRange f (by simp [f])) (y.mapRange f (by simp [f])) ?_
  · ext i
    exact hinj congr($this i)
  simpa [Finsupp.linearCombination, f, Finsupp.sum_mapRange_index]

variable (R) in
/-
**LinearIndependent.restrict_scalars'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.restrict_scalars' [Semiring K] [SMulWithZero R K] [Modul
e K M] [IsScalarTower R K M] [FaithfulSMul R K] [IsScalarTower R K K] {v : ι -> 
M} (li : LinearIndependent K v) : LinearIndependent R v
参数：li : LinearIndependent K v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndependent.restrict_scalars`：LinearIndependent.restrict_scalars [
Semiring K] [SMulWithZero R K] [Module K M] [IsScalarTower R K M] (hinj : Inject
ive fun r : R => r • (1 …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `faithfulSMul_iff_injective_smul_one`：faithfulSMul_iff_injective_smul_one
 (R A : Type*) [MulOneClass A] [SMul R A] [IsScalarTower R A A] : FaithfulSMul R
 A ↔ Injective (fun r : R…
-/
theorem LinearIndependent.restrict_scalars' [Semiring K] [SMulWithZero R K] [Module K M]
    [IsScalarTower R K M] [FaithfulSMul R K] [IsScalarTower R K K] {v : ι → M}
    (li : LinearIndependent K v) : LinearIndependent R v :=
  restrict_scalars ((faithfulSMul_iff_injective_smul_one R K).mp inferInstance) li

/-- If `v` is an injective family of vectors such that `f ∘ v` is linearly independent, then `v`
    spans a submodule disjoint from the kernel of `f`.
TODO : `LinearIndepOn` version. -/
/-
**Submodule.range_ker_disjoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.range_ker_disjoint {f : M ->ₗ[R] M'} (hv : LinearIndependent R (
f ∘ v)) : Disjoint (span R (range v)) (LinearMap.ker f)
参数：hv : LinearIndependent R (f ∘ v)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_iff_inf_le`：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Finsupp.span_image_eq_map_linearCombination`：span_image_eq_map_linearCom
bination (s : Set α) : span R (v '' s) = Submodule.map (linearCombination R v) (
supported R R s)
· 使用定理 `Submodule.map_inf_eq_map_inf_comap`：map_inf_eq_map_inf_comap [RingHomSur
jective σ₁₂] {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M} {p' : Submodule R₂ M₂} : m
ap f p ⊓ p' = map f (p ⊓…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.ker_comp`：ker_comp (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) 
: ker (g.comp f : M ->ₛₗ[τ₁₃] M₃) = comap f (ker g)
· 使用定理 `LinearMap.ker_eq_bot_of_injective`：ker_eq_bot_of_injective {f : M ->ₛₗ[τ
₁₂] M₂} (hf : Injective f) : ker f = ⊥
· 使用定理 `Finsupp.linearCombination_linear_comp`：linearCombination_linear_comp (f 
: M ->ₗ[R] M') : linearCombination R (f ∘ v) = f ∘ₗ linearCombination R v
· 使用定理 `LinearIndependent.eq_1`：∀ {ι : Type u'} (R : Type u_2) {M : Type u_4} (v
 : ι → M) [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Modu
le R M], Lin…
· 使用定理 `inf_bot_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderBo
t α] (a : α), a ⊓ ⊥ = ⊥
· 使用定理 `Submodule.map_bot`：map_bot (f : M ->ₛₗ[σ₁₂] M₂) : map f ⊥ = ⊥
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
If `v` is an injective family of vectors such that `f ∘ v` is linearly independe
nt, then `v`
    spans a submodule disjoint from the kernel of `f`.
TODO : `LinearIndepOn` version.
-/
theorem Submodule.range_ker_disjoint {f : M →ₗ[R] M'}
    (hv : LinearIndependent R (f ∘ v)) :
    Disjoint (span R (range v)) (LinearMap.ker f) := by
  rw [LinearIndependent, Finsupp.linearCombination_linear_comp] at hv
  rw [disjoint_iff_inf_le, ← Set.image_univ, Finsupp.span_image_eq_map_linearCombination,
    map_inf_eq_map_inf_comap, (LinearMap.ker_comp _ _).symm.trans
      (LinearMap.ker_eq_bot_of_injective hv), inf_bot_eq, map_bot]

/-- If `M / R` and `M' / R'` are modules, `i : R' → R` is a map, `j : M →+ M'` is a monoid map,
such that they are both injective, and compatible with the scalar
multiplications on `M` and `M'`, then `j` sends linearly independent families of vectors to
linearly independent families of vectors. As a special case, taking `R = R'`
it is `LinearIndependent.map_injOn`.
TODO : `LinearIndepOn` version. -/
/-
**LinearIndependent.map_of_injective_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.map_of_injective_injective {R' M' : Type*} [Ring R'] [Ad
dCommGroup M'] [Module R' M'] (hv : LinearIndependent R v) (i : R' -> R) (j : M 
->+ M') (hi : forall r, i r = 0 -> r = 0) (hj : forall m, j m = 0 -> m = 0) (hc 
: forall (r : R') (m : M), j (i r • m) = r • j m) : LinearIndependent R' (j ∘ v)
参数：hv : LinearIndependent R v；i : R' -> R；j : M ->+ M'；hi : forall r, i r = 0 ->
 r = 0；hj : forall m, j m = 0 -> m = 0；hc : forall (r : R') (m : M), j (i r • m)
 = r • j m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `linearIndependent_iff'`：linearIndependent_iff'ₛ : LinearIndependent R v 
↔ forall s : Finset ι, forall f g : ι -> R, ∑ i in s, f i • v i = ∑ i in s, g i 
• v i -> for…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `M / R` and `M' / R'` are modules, `i : R' → R` is a map, `j : M →+ M'` is a 
monoid map,
such that they are both injective, and compatible with the scalar
multiplications on `M` and `M'`, then `j` sends linearly independent families of
 vectors to
linearly independent families of vectors. As a special case, taking `R = R'`
it is `LinearIndependent.map_injOn`.
TODO : `LinearIndepOn` version.
-/
theorem LinearIndependent.map_of_injective_injectiveₛ {R' M' : Type*}
    [Semiring R'] [AddCommMonoid M'] [Module R' M'] (hv : LinearIndependent R v)
    (i : R' → R) (j : M →+ M') (hi : Injective i) (hj : Injective j)
    (hc : ∀ (r : R') (m : M), j (i r • m) = r • j m) : LinearIndependent R' (j ∘ v) := by
  rw [linearIndependent_iff'ₛ] at hv ⊢
  intro S r₁ r₂ H s hs
  simp_rw [comp_apply, ← hc, ← map_sum] at H
  exact hi <| hv _ _ _ (hj H) s hs

/-- If `M / R` and `M' / R'` are modules, `i : R → R'` is a surjective map,
and `j : M →+ M'` is an injective monoid map, such that the scalar multiplications
on `M` and `M'` are compatible, then `j` sends linearly independent families
of vectors to linearly independent families of vectors. As a special case, taking `R = R'`
it is `LinearIndependent.map_injOn`.
TODO : `LinearIndepOn` version. -/
/-
**LinearIndependent.map_of_surjective_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.map_of_surjective_injective {R' M' : Type*} [Semiring R'
] [AddCommMonoid M'] [Module R' M'] (hv : LinearIndependent R v) (i : R -> R') (
j : M ->+ M') (hi : Surjective i) (hj : forall m, j m = 0 -> m = 0) (hc : forall
 (r : R) (m : M), j (r • m) = i r • j m) : LinearIndependent R' (j ∘ v)
参数：hv : LinearIndependent R v；i : R -> R'；j : M ->+ M'；hi : Surjective i；hj : fo
rall m, j m = 0 -> m = 0；hc : forall (r : R) (m : M), j (r • m) = i r • j m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndependent.map_of_surjective_injectiveₛ`：LinearIndependent.map_of
_surjective_injectiveₛ {R' M' : Type*} [Semiring R'] [AddCommMonoid M'] [Module 
R' M'] (hv : LinearIndependent R v) …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `injective_iff_map_eq_zero`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9
} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [AddM
onoidHomClass F…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N

--- 原说明 ---
If `M / R` and `M' / R'` are modules, `i : R → R'` is a surjective map,
and `j : M →+ M'` is an injective monoid map, such that the scalar multiplicatio
ns
on `M` and `M'` are compatible, then `j` sends linearly independent families
of vectors to linearly independent families of vectors. As a special case, takin
g `R = R'`
it is `LinearIndependent.map_injOn`.
TODO : `LinearIndepOn` version.
-/
theorem LinearIndependent.map_of_surjective_injectiveₛ {R' M' : Type*}
    [Semiring R'] [AddCommMonoid M'] [Module R' M'] (hv : LinearIndependent R v)
    (i : R → R') (j : M →+ M') (hi : Surjective i) (hj : Injective j)
    (hc : ∀ (r : R) (m : M), j (r • m) = i r • j m) : LinearIndependent R' (j ∘ v) := by
  obtain ⟨i', hi'⟩ := hi.hasRightInverse
  refine hv.map_of_injective_injectiveₛ i' j (fun _ _ h ↦ ?_) hj fun r m ↦ ?_
  · apply_fun i at h
    rwa [hi', hi'] at h
  rw [hc (i' r) m, hi']

/-- If a linear map is injective on the span of a family of linearly independent vectors, then
the family stays linearly independent after composing with the linear map.
See `LinearIndependent.map` for the version with `Set.InjOn` replaced by `Disjoint`
when working over a ring. -/
/-
**LinearIndependent.map_injOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.map_injOn (hv : LinearIndependent R v) (f : M ->ₗ[R] M')
 (hf_inj : Set.InjOn f (span R (Set.range v))) : LinearIndependent R (f ∘ v)
参数：hv : LinearIndependent R v；f : M ->ₗ[R] M'；hf_inj : Set.InjOn f (span R (Set.
range v))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.linearIndependent_iff_of_injOn`：∀ {ι : Type u'} {R : Type u_2}
 {M : Type u_4} {M' : Type u_5} {v : ι → M} [inst : Semiring R] [inst_1 : AddCom
mMonoid M]   [inst_2 : AddComm…

--- 原说明 ---
If a linear map is injective on the span of a family of linearly independent vec
tors, then
the family stays linearly independent after composing with the linear map.
See `LinearIndependent.map` for the version with `Set.InjOn` replaced by `Disjoi
nt`
when working over a ring.
-/
theorem LinearIndependent.map_injOn (hv : LinearIndependent R v) (f : M →ₗ[R] M')
    (hf_inj : Set.InjOn f (span R (Set.range v))) : LinearIndependent R (f ∘ v) :=
  (f.linearIndependent_iff_of_injOn hf_inj).mpr hv
/-
**LinearIndepOn.map_injOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndepOn.map_injOn (hv : LinearIndepOn R v s) (f : M ->ₗ[R] M') (hf_i
nj : Set.InjOn f (span R (v '' s))) : LinearIndepOn R (f ∘ v) s
参数：hv : LinearIndepOn R v s；f : M ->ₗ[R] M'；hf_inj : Set.InjOn f (span R (v '' s
))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.linearIndepOn_iff_of_injOn`：∀ {ι : Type u'} {R : Type u_2} {s 
: Set ι} {M : Type u_4} {M' : Type u_5} {v : ι → M} [inst : Semiring R]   [inst_
1 : AddCommMonoid M] [inst…
-/
theorem LinearIndepOn.map_injOn (hv : LinearIndepOn R v s) (f : M →ₗ[R] M')
    (hf_inj : Set.InjOn f (span R (v '' s))) : LinearIndepOn R (f ∘ v) s :=
  (f.linearIndepOn_iff_of_injOn hf_inj).mpr hv
/-
**LinearIndepOn.comp_of_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndepOn.comp_of_image {s : Set ι'} {f : ι' -> ι} (h : LinearIndepOn 
R v (f '' s)) (hf : InjOn f s) : LinearIndepOn R (v ∘ f) s
参数：h : LinearIndepOn R v (f '' s)；hf : InjOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndependent.comp`：LinearIndependent.comp (h : LinearIndependent R 
v) (f : ι' -> ι) (hf : Injective f) : LinearIndependent R (v ∘ f)
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
theorem LinearIndepOn.comp_of_image {s : Set ι'} {f : ι' → ι} (h : LinearIndepOn R v (f '' s))
    (hf : InjOn f s) : LinearIndepOn R (v ∘ f) s :=
  LinearIndependent.comp h _ (Equiv.Set.imageOfInjOn _ _ hf).injective
/-
**LinearIndepOn.image_of_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndepOn.image_of_comp (f : ι -> ι') (g : ι' -> M) (hs : LinearIndepO
n R (g ∘ f) s) : LinearIndepOn R g (f '' s)
参数：f : ι -> ι'；g : ι' -> M；hs : LinearIndepOn R (g ∘ f) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.injOn_iff_injective`：injOn_iff_injective : InjOn f s ↔ Injective (s.
domRestrict f)
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `LinearIndependent.injective`：LinearIndependent.injective [Nontrivial R] 
(hv : LinearIndependent R v) : Injective v
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `linearIndependent_equiv'`：linearIndependent_equiv' (e : ι ≃ ι') {f : ι' 
-> M} {g : ι -> M} (h : f ∘ e = g) : LinearIndependent R g ↔ LinearIndependent R
 f
-/
theorem LinearIndepOn.image_of_comp (f : ι → ι') (g : ι' → M) (hs : LinearIndepOn R (g ∘ f) s) :
    LinearIndepOn R g (f '' s) := by
  nontriviality R
  have : InjOn f s := injOn_iff_injective.2 hs.injective.of_comp
  exact (linearIndependent_equiv' (Equiv.Set.imageOfInjOn f s this) rfl).1 hs
/-
**LinearIndepOn.id_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndepOn.id_image (hs : LinearIndepOn R v s) : LinearIndepOn R id (v 
'' s)
参数：hs : LinearIndepOn R v s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndepOn.image_of_comp`：LinearIndepOn.image_of_comp (f : ι -> ι') (
g : ι' -> M) (hs : LinearIndepOn R (g ∘ f) s) : LinearIndepOn R g (f '' s)
-/
theorem LinearIndepOn.id_image (hs : LinearIndepOn R v s) : LinearIndepOn R id (v '' s) :=
  LinearIndepOn.image_of_comp v id hs
/-
**LinearIndepOn_iff_linearIndepOn_image_injOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndepOn_iff_linearIndepOn_image_injOn [Nontrivial R] : LinearIndepOn
 R v s ↔ LinearIndepOn R id (v '' s) ∧ InjOn v s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndepOn.id_image`：LinearIndepOn.id_image (hs : LinearIndepOn R v s
) : LinearIndepOn R id (v '' s)
· 使用定理 `LinearIndepOn.injOn`：LinearIndepOn.injOn [Nontrivial R] (hv : LinearInde
pOn R v s) : InjOn v s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `linearIndepOn_iff_image`：linearIndepOn_iff_image {ι} {s : Set ι} {f : ι 
-> M} (hf : Set.InjOn f s) : LinearIndepOn R f s ↔ LinearIndepOn R id (f '' s)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem LinearIndepOn_iff_linearIndepOn_image_injOn [Nontrivial R] :
    LinearIndepOn R v s ↔ LinearIndepOn R id (v '' s) ∧ InjOn v s :=
  ⟨fun h ↦ ⟨h.id_image, h.injOn⟩, fun h ↦ (linearIndepOn_iff_image h.2).2 h.1⟩
/-
**linearIndepOn_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndepOn_congr {w : ι -> M} (h : EqOn v w s) : LinearIndepOn R v s ↔ 
LinearIndepOn R w s
参数：h : EqOn v w s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearIndepOn.eq_1`：∀ {ι : Type u'} (R : Type u_2) {M : Type u_4} (v : ι
 → M) [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R
 M] (s :…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.EqOn.symm`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : α → 
β}, Set.EqOn f₁ f₂ s → Set.EqOn f₂ f₁ s
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem linearIndepOn_congr {w : ι → M} (h : EqOn v w s) :
    LinearIndepOn R v s ↔ LinearIndepOn R w s := by
  rw [LinearIndepOn, LinearIndepOn]
  convert! Iff.rfl using 2
  ext x
  exact h.symm x.2
/-
**LinearIndepOn.congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndepOn.congr {w : ι -> M} (hli : LinearIndepOn R v s) (h : EqOn v w
 s) : LinearIndepOn R w s
参数：hli : LinearIndepOn R v s；h : EqOn v w s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `linearIndepOn_congr`：linearIndepOn_congr {w : ι -> M} (h : EqOn v w s) :
 LinearIndepOn R v s ↔ LinearIndepOn R w s
-/
theorem LinearIndepOn.congr {w : ι → M} (hli : LinearIndepOn R v s) (h : EqOn v w s) :
    LinearIndepOn R w s :=
  (linearIndepOn_congr h).1 hli
/-
**LinearIndependent.group_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.group_smul {G : Type*} [hG : Group G] [MulAction G R] [S
Mul G M] [IsScalarTower G R M] [SMulCommClass G R M] {v : ι -> M} (hv : LinearIn
dependent R v) (w : ι -> G) : LinearIndependent R (w • v)
参数：hv : LinearIndependent R v；w : ι -> G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `linearIndependent_iff''ₛ`：∀ {ι : Type u'} {R : Type u_2} {M : Type u_4} 
{v : ι → M} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Mo
dule R M],   L…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `IsUnit.smul_left_cancel`：smul_left_cancel {a : α} (ha : IsUnit a) {x y :
 β} : a • x = a • y ↔ x = y
· 使用引理 `Group.isUnit`：Group.isUnit [Group α] (a : α) : IsUnit a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
theorem LinearIndependent.group_smul {G : Type*} [hG : Group G] [MulAction G R]
    [SMul G M] [IsScalarTower G R M] [SMulCommClass G R M] {v : ι → M}
    (hv : LinearIndependent R v) (w : ι → G) : LinearIndependent R (w • v) := by
  rw [linearIndependent_iff''ₛ] at hv ⊢
  intro s g₁ g₂ hgs hsum i
  refine (Group.isUnit (w i)).smul_left_cancel.mp ?_
  refine hv s (fun i ↦ w i • g₁ i) (fun i ↦ w i • g₂ i) (fun i hi ↦ ?_) ?_ i
  · simp_rw [hgs i hi]
  · simpa only [smul_assoc, smul_comm] using! hsum

@[simp]
/-
**LinearIndependent.group_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.group_smul_iff {G : Type*} [hG : Group G] [MulAction G R
] [MulAction G M] [IsScalarTower G R M] [SMulCommClass G R M] (v : ι -> M) (w : 
ι -> G) : LinearIndependent R (w • v) ↔ LinearIndependent R v
参数：v : ι -> M；w : ι -> G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `LinearIndependent.group_smul`：LinearIndependent.group_smul {G : Type*} [
hG : Group G] [MulAction G R] [SMul G M] [IsScalarTower G R M] [SMulCommClass G 
R M] {v : ι -> M} …
-/
theorem LinearIndependent.group_smul_iff {G : Type*} [hG : Group G] [MulAction G R]
    [MulAction G M] [IsScalarTower G R M] [SMulCommClass G R M] (v : ι → M) (w : ι → G) :
    LinearIndependent R (w • v) ↔ LinearIndependent R v := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.group_smul w⟩
  convert! h.group_smul (fun i ↦ (w i)⁻¹)
  simp [funext_iff]

-- This lemma cannot be proved with `LinearIndependent.group_smul` since the action of
-- `Rˣ` on `R` is not commutative.
/-
**LinearIndependent.units_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.units_smul {v : ι -> M} (hv : LinearIndependent R v) (w 
: ι -> Rˣ) : LinearIndependent R (w • v)
参数：hv : LinearIndependent R v；w : ι -> Rˣ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `linearIndependent_iff''ₛ`：∀ {ι : Type u'} {R : Type u_2} {M : Type u_4} 
{v : ι → M} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Mo
dule R M],   L…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.mul_left_inj`：mul_left_inj (a : αˣ) {b c : α} : b * a = c * a ↔ b 
= c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
-/
theorem LinearIndependent.units_smul {v : ι → M} (hv : LinearIndependent R v) (w : ι → Rˣ) :
    LinearIndependent R (w • v) := by
  rw [linearIndependent_iff''ₛ] at hv ⊢
  intro s g₁ g₂ hgs hsum i
  rw [← (w i).mul_left_inj]
  refine hv s (fun i ↦ g₁ i • w i) (fun i ↦ g₂ i • w i) (fun i hi ↦ ?_) ?_ i
  · simp_rw [hgs i hi]
  · simpa only [smul_eq_mul, mul_smul, Pi.smul_apply'] using! hsum

@[simp]
/-
**LinearIndependent.units_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.units_smul_iff (v : ι -> M) (w : ι -> Rˣ) : LinearIndepe
ndent R (w • v) ↔ LinearIndependent R v
参数：v : ι -> M；w : ι -> Rˣ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `LinearIndependent.units_smul`：LinearIndependent.units_smul {v : ι -> M} 
(hv : LinearIndependent R v) (w : ι -> Rˣ) : LinearIndependent R (w • v)
-/
theorem LinearIndependent.units_smul_iff (v : ι → M) (w : ι → Rˣ) :
    LinearIndependent R (w • v) ↔ LinearIndependent R v := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.units_smul w⟩
  convert! h.units_smul (fun i ↦ (w i)⁻¹)
  simp [funext_iff]
/-
**linearIndependent_span** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndependent_span (hs : LinearIndependent R v) : LinearIndependent R 
(M
参数：hs : LinearIndependent R v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndependent.of_comp`：LinearIndependent.of_comp (f : M ->ₗ[R] M') (
hfv : LinearIndependent R (f ∘ v)) : LinearIndependent R v
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
theorem linearIndependent_span (hs : LinearIndependent R v) :
    LinearIndependent R (M := span R (range v))
      (fun i : ι ↦ ⟨v i, subset_span (mem_range_self i)⟩) :=
  LinearIndependent.of_comp (span R (range v)).subtype hs

/-- Every finite subset of a linearly independent set is linearly independent. -/
/-
**linearIndependent_finset_map_embedding_subtype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndependent_finset_map_embedding_subtype (s : Set M) (li : LinearInd
ependent R ((↑) : s -> M)) (t : Finset s) : LinearIndependent R ((↑) : Finset.ma
p (Embedding.subtype (· in s)) t -> M)
参数：s : Set M；li : LinearIndependent R ((↑) : s -> M)；t : Finset s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndependent.comp`：LinearIndependent.comp (h : LinearIndependent R 
v) (f : ι' -> ι) (hf : Injective f) : LinearIndependent R (v ∘ f)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
Every finite subset of a linearly independent set is linearly independent.
-/
theorem linearIndependent_finset_map_embedding_subtype (s : Set M)
    (li : LinearIndependent R ((↑) : s → M)) (t : Finset s) :
    LinearIndependent R ((↑) : Finset.map (Embedding.subtype (· ∈ s)) t → M) :=
  li.comp (fun _ ↦ ⟨_, by aesop⟩) <| by intro; simp

section Indexed

/-
**linearIndepOn_of_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndepOn_of_finite (s : Set ι) (H : forall t subseteq s, Set.Finite t
 -> LinearIndepOn R v t) : LinearIndepOn R v s
参数：s : Set ι；H : forall t subseteq s, Set.Finite t -> LinearIndepOn R v t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `linearIndepOn_iffₛ`：linearIndepOn_iffₛ : LinearIndepOn R v s ↔ forall f 
in Finsupp.supported R R s, forall g in Finsupp.supported R R s, Finsupp.linearC
ombinati…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
-/
theorem linearIndepOn_of_finite (s : Set ι) (H : ∀ t ⊆ s, Set.Finite t → LinearIndepOn R v t) :
    LinearIndepOn R v s :=
  linearIndepOn_iffₛ.2 fun f hf g hg eq ↦
    linearIndepOn_iffₛ.1 (H _ (union_subset hf hg) <| (Finset.finite_toSet _).union <|
      Finset.finite_toSet _) f Set.subset_union_left g Set.subset_union_right eq

end Indexed

/-- Linear independent families are injective, even if you multiply either side. -/
/-
**LinearIndependent.eq_of_smul_apply_eq_smul_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.eq_of_smul_apply_eq_smul_apply {M : Type*} [AddCommMonoi
d M] [Module R M] {v : ι -> M} (li : LinearIndependent R v) (c d : R) (i j : ι) 
(hc : c != 0) (h : c • v i = d • v j) : i = j
参数：li : LinearIndependent R v；c d : R；i j : ι；hc : c != 0；h : c • v i = d • v j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.single_eq_single_iff`：single_eq_single_iff (a₁ a₂ : α) (b₁ b₂ : 
M) : single a₁ b₁ = single a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ ∨ b₁ = 0 ∧ b₂ = 0

--- 原说明 ---
Linear independent families are injective, even if you multiply either side.
-/
theorem LinearIndependent.eq_of_smul_apply_eq_smul_apply {M : Type*} [AddCommMonoid M] [Module R M]
    {v : ι → M} (li : LinearIndependent R v) (c d : R) (i j : ι) (hc : c ≠ 0)
    (h : c • v i = d • v j) : i = j := by
  have h_single_eq : Finsupp.single i c = Finsupp.single j d :=
    li <| by simpa [Finsupp.linearCombination_apply] using h
  rcases (Finsupp.single_eq_single_iff ..).mp h_single_eq with (⟨H, _⟩ | ⟨hc, _⟩)
  · exact H
  · contradiction

section Subtype

/-! The following lemmas use the subtype defined by a set in `M` as the index set `ι`. -/

/-
**LinearIndependent.disjoint_span_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.disjoint_span_image (hv : LinearIndependent R v) {s t : 
Set ι} (hs : Disjoint s t) : Disjoint (Submodule.span R <| v '' s) (Submodule.sp
an R <| v '' t)
参数：hv : LinearIndependent R v；hs : Disjoint s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.disjoint_def`：disjoint_def {p p' : Submodule R M} : Disjoint p
 p' ↔ forall x in p, x in p' -> x = (0 : M)
· 使用定理 `Finsupp.disjoint_supported_supported`：disjoint_supported_supported {s t 
: Set α} (h : Disjoint s t) : Disjoint (supported M R s) (supported M R t)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `LinearIndependent.finsuppLinearCombination_injective`：∀ {ι : Type u'} {R
 : Type u_2} {M : Type u_4} {v : ι → M} [inst : Semiring R] [inst_1 : AddCommMon
oid M]   [inst_2 : _root_.Module R M], Lin…

--- 原说明 ---
The following lemmas use the subtype defined by a set in `M` as the index set `ι
`.
-/
theorem LinearIndependent.disjoint_span_image (hv : LinearIndependent R v) {s t : Set ι}
    (hs : Disjoint s t) : Disjoint (Submodule.span R <| v '' s) (Submodule.span R <| v '' t) := by
  simp only [disjoint_def, Finsupp.mem_span_image_iff_linearCombination]
  rintro _ ⟨l₁, hl₁, rfl⟩ ⟨l₂, hl₂, H⟩
  rw [hv.finsuppLinearCombination_injective.eq_iff] at H; subst l₂
  have : l₁ = 0 := Submodule.disjoint_def.mp (Finsupp.disjoint_supported_supported hs) _ hl₁ hl₂
  simp [this]
/-
**LinearIndependent.notMem_span_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.notMem_span_image [Nontrivial R] (hv : LinearIndependent
 R v) {s : Set ι} {x : ι} (h : x ∉ s) : v x ∉ Submodule.span R (v '' s)
参数：hv : LinearIndependent R v；h : x ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `Submodule.mem_span_singleton_self`：mem_span_singleton_self (x : M) : x i
n R ∙ x
· 使用定理 `LinearIndependent.ne_zero`：LinearIndependent.ne_zero [Nontrivial R] (i :
 ι) (hv : LinearIndependent R v) : v i != 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.disjoint_def`：disjoint_def {p p' : Submodule R M} : Disjoint p
 p' ↔ forall x in p, x in p' -> x = (0 : M)
· 使用定理 `LinearIndependent.disjoint_span_image`：LinearIndependent.disjoint_span_i
mage (hv : LinearIndependent R v) {s t : Set ι} (hs : Disjoint s t) : Disjoint (
Submodule.span R <| v '' s)…
-/
theorem LinearIndependent.notMem_span_image [Nontrivial R] (hv : LinearIndependent R v) {s : Set ι}
    {x : ι} (h : x ∉ s) : v x ∉ Submodule.span R (v '' s) := by
  have h' : v x ∈ Submodule.span R (v '' {x}) := by
    rw [Set.image_singleton]
    exact mem_span_singleton_self (v x)
  intro w
  apply LinearIndependent.ne_zero x hv
  refine disjoint_def.1 (hv.disjoint_span_image ?_) (v x) h' w
  simpa using h
/-
**LinearIndependent.linearCombination_ne_of_notMem_support** 是 Mathlib 中的一个定理，位于
命名空间 ``。
形式化陈述：LinearIndependent.linearCombination_ne_of_notMem_support [Nontrivial R] (h
v : LinearIndependent R v) {x : ι} (f : ι ->₀ R) (h : x ∉ f.support) : f.linearC
ombination R v != v x
参数：hv : LinearIndependent R v；f : ι ->₀ R；h : x ∉ f.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finsupp.span_image_eq_map_linearCombination`：span_image_eq_map_linearCom
bination (s : Set α) : span R (v '' s) = Submodule.map (linearCombination R v) (
supported R R s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `LinearIndependent.notMem_span_image`：LinearIndependent.notMem_span_image
 [Nontrivial R] (hv : LinearIndependent R v) {s : Set ι} {x : ι} (h : x ∉ s) : v
 x ∉ Submodule.span R (v …
· 使用定理 `Finsupp.mem_supported_support`：mem_supported_support (p : α ->₀ M) : p i
n Finsupp.supported M R (p.support : Set α)
-/
theorem LinearIndependent.linearCombination_ne_of_notMem_support [Nontrivial R]
    (hv : LinearIndependent R v) {x : ι} (f : ι →₀ R) (h : x ∉ f.support) :
    f.linearCombination R v ≠ v x := by
  replace h : x ∉ (f.support : Set ι) := h
  intro w
  have p : ∀ x ∈ Finsupp.supported R R f.support,
    Finsupp.linearCombination R v x ≠ f.linearCombination R v := by
    simpa [← w, Finsupp.span_image_eq_map_linearCombination] using hv.notMem_span_image h
  exact p f (f.mem_supported_support R) rfl

end Subtype

/-
**LinearIndepOn.id_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndepOn.id_image (hs : LinearIndepOn R v s) : LinearIndepOn R id (v 
'' s)
参数：hs : LinearIndepOn R v s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndepOn.image_of_comp`：LinearIndepOn.image_of_comp (f : ι -> ι') (
g : ι' -> M) (hs : LinearIndepOn R (g ∘ f) s) : LinearIndepOn R g (f '' s)
-/
theorem LinearIndepOn.id_imageₛ {s : Set M} {f : M →ₗ[R] M'} (hs : LinearIndepOn R id s)
    (hf_inj : Set.InjOn f (span R s)) : LinearIndepOn R id (f '' s) :=
  id_image <| hs.map_injOn f (by simpa using hf_inj)
/-
**surjective_of_linearIndependent_of_span** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：surjective_of_linearIndependent_of_span [Nontrivial R] (hv : LinearIndepen
dent R v) (f : ι' ↪ ι) (hss : range v subseteq span R (range (v ∘ f))) : Surject
ive f
参数：hv : LinearIndependent R v；f : ι' ↪ ι；hss : range v subseteq span R (range (v
 ∘ f))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndependent.comp`：LinearIndependent.comp (h : LinearIndependent R 
v) (f : ι' -> ι) (hf : Injective f) : LinearIndependent R (v ∘ f)
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.linearCombination_mapDomain`：linearCombination_mapDomain (f : α 
-> α') (l : α ->₀ R) : (linearCombination R v') (mapDomain f l) = (linearCombina
tion R (v' ∘ f)) l
· 使用定理 `LinearIndependent.linearCombination_repr`：LinearIndependent.linearCombin
ation_repr (x) : Finsupp.linearCombination R v (hv.repr x) = x
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Finsupp.single_of_embDomain_single`：single_of_embDomain_single (l : α ->
₀ M) (f : α ↪ β) (a : β) (b : M) (hb : b != 0) (h : l.embDomain f = single a b) 
: exists x, l = single x…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.embDomain_eq_mapDomain`：embDomain_eq_mapDomain (f : α ↪ β) (v : 
α ->₀ M) : embDomain f v = mapDomain f v
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem surjective_of_linearIndependent_of_span [Nontrivial R] (hv : LinearIndependent R v)
    (f : ι' ↪ ι) (hss : range v ⊆ span R (range (v ∘ f))) : Surjective f := by
  intro i
  let repr : (span R (range (v ∘ f)) : Type _) → ι' →₀ R := (hv.comp f f.injective).repr
  let l := (repr ⟨v i, hss (mem_range_self i)⟩).mapDomain f
  have h_total_l : Finsupp.linearCombination R v l = v i := by
    dsimp only [l]
    rw [Finsupp.linearCombination_mapDomain]
    rw [(hv.comp f f.injective).linearCombination_repr]
  have h_total_eq : Finsupp.linearCombination R v l = Finsupp.linearCombination R v
       (Finsupp.single i 1) := by
    rw [h_total_l, Finsupp.linearCombination_single, one_smul]
  have l_eq : l = _ := hv h_total_eq
  dsimp only [l] at l_eq
  rw [← Finsupp.embDomain_eq_mapDomain] at l_eq
  rcases Finsupp.single_of_embDomain_single (repr ⟨v i, _⟩) f i (1 : R) zero_ne_one.symm l_eq with
    ⟨i', hi'⟩
  use i'
  exact hi'.2

set_option backward.isDefEq.respectTransparency false in
/-
**eq_of_linearIndepOn_id_of_span_subtype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_of_linearIndepOn_id_of_span_subtype [Nontrivial R] {s t : Set M} (hs : 
LinearIndepOn R id s) (h : t subseteq s) (hst : s subseteq span R t) : s = t
参数：hs : LinearIndepOn R id s；h : t subseteq s；hst : s subseteq span R t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `Subtype.mk.inj`：∀ {α : Sort u} {p : α → Prop} {val : α} {property : p va
l} {val_1 : α} {property_1 : p val_1},   ⟨val, property⟩ = ⟨val_1, property_1⟩ →
 val…
· 使用定理 `surjective_of_linearIndependent_of_span`：surjective_of_linearIndependent
_of_span [Nontrivial R] (hv : LinearIndependent R v) (f : ι' ↪ ι) (hss : range v
 subseteq span R (range (v ∘ …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Subtype.mem`：Subtype.mem {α : Type*} {s : Set α} (p : s) : (p : α) in s
-/
theorem eq_of_linearIndepOn_id_of_span_subtype [Nontrivial R] {s t : Set M}
    (hs : LinearIndepOn R id s) (h : t ⊆ s) (hst : s ⊆ span R t) : s = t := by
  let f : t ↪ s :=
    ⟨fun x => ⟨x.1, h x.2⟩, fun a b hab => Subtype.coe_injective (Subtype.mk.inj hab)⟩
  have h_surj : Surjective f := by
    apply surjective_of_linearIndependent_of_span hs f _
    convert! hst <;> simp [f, comp_def]
  change s = t
  apply Subset.antisymm _ h
  intro x hx
  rcases h_surj ⟨x, hx⟩ with ⟨y, hy⟩
  convert! y.mem
  rw [← Subtype.mk.inj hy]
/-
**le_of_span_le_span** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_of_span_le_span [Nontrivial R] {s t u : Set M} (hl : LinearIndepOn R id
 u) (hsu : s subseteq u) (htu : t subseteq u) (hst : span R s <= span R t) : s s
ubseteq t
参数：hl : LinearIndepOn R id u；hsu : s subseteq u；htu : t subseteq u；hst : span R 
s <= span R t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_linearIndepOn_id_of_span_subtype`：eq_of_linearIndepOn_id_of_span_s
ubtype [Nontrivial R] {s t : Set M} (hs : LinearIndepOn R id s) (h : t subseteq 
s) (hst : s subseteq span R …
· 使用引理 `LinearIndepOn.mono`：LinearIndepOn.mono {t s : Set ι} (hs : LinearIndepOn
 R v s) (h : t subseteq s) : LinearIndepOn R v t
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
-/
theorem le_of_span_le_span [Nontrivial R] {s t u : Set M} (hl : LinearIndepOn R id u)
    (hsu : s ⊆ u) (htu : t ⊆ u) (hst : span R s ≤ span R t) : s ⊆ t := by
  have :=
    eq_of_linearIndepOn_id_of_span_subtype (hl.mono (Set.union_subset hsu htu))
      Set.subset_union_right (Set.union_subset (Set.Subset.trans subset_span hst) subset_span)
  rw [← this]; apply Set.subset_union_left
/-
**span_le_span_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：span_le_span_iff [Nontrivial R] {s t u : Set M} (hl : LinearIndependent R 
((↑) : u -> M)) (hsu : s subseteq u) (htu : t subseteq u) : span R s <= span R t
 ↔ s subseteq t
参数：hl : LinearIndependent R ((↑) : u -> M)；hsu : s subseteq u；htu : t subseteq u
。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_span_le_span`：le_of_span_le_span [Nontrivial R] {s t u : Set M} (h
l : LinearIndepOn R id u) (hsu : s subseteq u) (htu : t subseteq u) (hst : span 
R s <= s…
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
-/
theorem span_le_span_iff [Nontrivial R] {s t u : Set M} (hl : LinearIndependent R ((↑) : u → M))
    (hsu : s ⊆ u) (htu : t ⊆ u) : span R s ≤ span R t ↔ s ⊆ t :=
  ⟨le_of_span_le_span hl hsu htu, span_mono⟩

end Semiring

section Module

variable {v : ι → M}
variable [Ring R] [AddCommGroup M] [AddCommGroup M']
variable [Module R M] [Module R M']

open Finset in
/-- If `∑ i, f i • v i = ∑ i, g i • v i`, then for all `i`, `f i = g i`. -/
/-
**LinearIndependent.eq_coords_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.eq_coords_of_eq [Fintype ι] {v : ι -> M} (hv : LinearInd
ependent R v) {f : ι -> R} {g : ι -> R} (heq : ∑ i, f i • v i = ∑ i, g i • v i) 
(i : ι) : f i = g i
参数：hv : LinearIndependent R v；heq : ∑ i, f i • v i = ∑ i, g i • v i；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `linearIndependent_iff'`：linearIndependent_iff'ₛ : LinearIndependent R v 
↔ forall s : Finset ι, forall f g : ι -> R, ∑ i in s, f i • v i = ∑ i in s, g i 
• v i -> for…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)

--- 原说明 ---
If `∑ i, f i • v i = ∑ i, g i • v i`, then for all `i`, `f i = g i`.
-/
theorem LinearIndependent.eq_coords_of_eq [Fintype ι] {v : ι → M} (hv : LinearIndependent R v)
    {f : ι → R} {g : ι → R} (heq : ∑ i, f i • v i = ∑ i, g i • v i) (i : ι) : f i = g i := by
  rw [← sub_eq_zero, ← sum_sub_distrib] at heq
  simp_rw [← sub_smul] at heq
  exact sub_eq_zero.mp ((linearIndependent_iff'.mp hv) univ (fun i ↦ f i - g i) heq i (mem_univ i))

/-- If `v` is a linearly independent family of vectors and the kernel of a linear map `f` is
disjoint with the submodule spanned by the vectors of `v`, then `f ∘ v` is a linearly independent
family of vectors. See also `LinearIndependent.map'` for a special case assuming `ker f = ⊥`. -/
/-
**LinearIndependent.map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.map (hv : LinearIndependent R v) {f : M ->ₗ[R] M'} (hf_i
nj : Disjoint (span R (range v)) (LinearMap.ker f)) : LinearIndependent R (f ∘ v
)
参数：hv : LinearIndependent R v；hf_inj : Disjoint (span R (range v)) (LinearMap.ke
r f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.linearIndependent_iff_of_disjoint`：∀ {ι : Type u'} {R : Type u
_2} {M : Type u_4} {M' : Type u_5} [inst : Ring R] [inst_1 : AddCommGroup M]   [
inst_2 : AddCommGroup M'] [inst_3…

--- 原说明 ---
If `v` is a linearly independent family of vectors and the kernel of a linear ma
p `f` is
disjoint with the submodule spanned by the vectors of `v`, then `f ∘ v` is a lin
early independent
family of vectors. See also `LinearIndependent.map'` for a special case assuming
 `ker f = ⊥`.
-/
theorem LinearIndependent.map (hv : LinearIndependent R v) {f : M →ₗ[R] M'}
    (hf_inj : Disjoint (span R (range v)) (LinearMap.ker f)) : LinearIndependent R (f ∘ v) :=
  (f.linearIndependent_iff_of_disjoint hf_inj).mpr hv

/-- An injective linear map sends linearly independent families of vectors to linearly independent
families of vectors. See also `LinearIndependent.map` for a more general statement. -/
/-
**LinearIndependent.map'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.map' (hv : LinearIndependent R v) (f : M ->ₗ[R] M') (hf_
inj : LinearMap.ker f = ⊥) : LinearIndependent R (f ∘ v)
参数：hv : LinearIndependent R v；f : M ->ₗ[R] M'；hf_inj : LinearMap.ker f = ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndependent.map`：LinearIndependent.map (hv : LinearIndependent R v
) {f : M ->ₗ[R] M'} (hf_inj : Disjoint (span R (range v)) (LinearMap.ker f)) : L
inearIndepe…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
An injective linear map sends linearly independent families of vectors to linear
ly independent
families of vectors. See also `LinearIndependent.map` for a more general stateme
nt.
-/
theorem LinearIndependent.map' (hv : LinearIndependent R v) (f : M →ₗ[R] M')
    (hf_inj : LinearMap.ker f = ⊥) : LinearIndependent R (f ∘ v) :=
  hv.map <| by simp_rw [hf_inj, disjoint_bot_right]

/-- If `M / R` and `M' / R'` are modules, `i : R' → R` is a map, `j : M →+ M'` is a monoid map,
such that they send non-zero elements to non-zero elements, and compatible with the scalar
multiplications on `M` and `M'`, then `j` sends linearly independent families of vectors to
linearly independent families of vectors. As a special case, taking `R = R'`
it is `LinearIndependent.map'`. -/
/-
**LinearIndependent.map_of_injective_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.map_of_injective_injective {R' M' : Type*} [Ring R'] [Ad
dCommGroup M'] [Module R' M'] (hv : LinearIndependent R v) (i : R' -> R) (j : M 
->+ M') (hi : forall r, i r = 0 -> r = 0) (hj : forall m, j m = 0 -> m = 0) (hc 
: forall (r : R') (m : M), j (i r • m) = r • j m) : LinearIndependent R' (j ∘ v)
参数：hv : LinearIndependent R v；i : R' -> R；j : M ->+ M'；hi : forall r, i r = 0 ->
 r = 0；hj : forall m, j m = 0 -> m = 0；hc : forall (r : R') (m : M), j (i r • m)
 = r • j m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `linearIndependent_iff'`：linearIndependent_iff'ₛ : LinearIndependent R v 
↔ forall s : Finset ι, forall f g : ι -> R, ∑ i in s, f i • v i = ∑ i in s, g i 
• v i -> for…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `M / R` and `M' / R'` are modules, `i : R' → R` is a map, `j : M →+ M'` is a 
monoid map,
such that they send non-zero elements to non-zero elements, and compatible with 
the scalar
multiplications on `M` and `M'`, then `j` sends linearly independent families of
 vectors to
linearly independent families of vectors. As a special case, taking `R = R'`
it is `LinearIndependent.map'`.
-/
theorem LinearIndependent.map_of_injective_injective {R' M' : Type*}
    [Ring R'] [AddCommGroup M'] [Module R' M'] (hv : LinearIndependent R v)
    (i : R' → R) (j : M →+ M') (hi : ∀ r, i r = 0 → r = 0) (hj : ∀ m, j m = 0 → m = 0)
    (hc : ∀ (r : R') (m : M), j (i r • m) = r • j m) : LinearIndependent R' (j ∘ v) := by
  rw [linearIndependent_iff'] at hv ⊢
  intro S r' H s hs
  simp_rw [comp_apply, ← hc, ← map_sum] at H
  exact hi _ <| hv _ _ (hj _ H) s hs

/-- If `M / R` and `M' / R'` are modules, `i : R → R'` is a surjective map which maps zero to zero,
`j : M →+ M'` is a monoid map which sends non-zero elements to non-zero elements, such that the
scalar multiplications on `M` and `M'` are compatible, then `j` sends linearly independent families
of vectors to linearly independent families of vectors. As a special case, taking `R = R'`
it is `LinearIndependent.map'`. -/
/-
**LinearIndependent.map_of_surjective_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.map_of_surjective_injective {R' M' : Type*} [Semiring R'
] [AddCommMonoid M'] [Module R' M'] (hv : LinearIndependent R v) (i : R -> R') (
j : M ->+ M') (hi : Surjective i) (hj : forall m, j m = 0 -> m = 0) (hc : forall
 (r : R) (m : M), j (r • m) = i r • j m) : LinearIndependent R' (j ∘ v)
参数：hv : LinearIndependent R v；i : R -> R'；j : M ->+ M'；hi : Surjective i；hj : fo
rall m, j m = 0 -> m = 0；hc : forall (r : R) (m : M), j (r • m) = i r • j m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndependent.map_of_surjective_injectiveₛ`：LinearIndependent.map_of
_surjective_injectiveₛ {R' M' : Type*} [Semiring R'] [AddCommMonoid M'] [Module 
R' M'] (hv : LinearIndependent R v) …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `injective_iff_map_eq_zero`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9
} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [AddM
onoidHomClass F…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N

--- 原说明 ---
If `M / R` and `M' / R'` are modules, `i : R → R'` is a surjective map which map
s zero to zero,
`j : M →+ M'` is a monoid map which sends non-zero elements to non-zero elements
, such that the
scalar multiplications on `M` and `M'` are compatible, then `j` sends linearly i
ndependent families
of vectors to linearly independent families of vectors. As a special case, takin
g `R = R'`
it is `LinearIndependent.map'`.
-/
theorem LinearIndependent.map_of_surjective_injective {R' M' : Type*}
    [Semiring R'] [AddCommMonoid M'] [Module R' M'] (hv : LinearIndependent R v)
    (i : R → R') (j : M →+ M') (hi : Surjective i) (hj : ∀ m, j m = 0 → m = 0)
    (hc : ∀ (r : R) (m : M), j (r • m) = i r • j m) : LinearIndependent R' (j ∘ v) :=
  hv.map_of_surjective_injectiveₛ i _ hi ((injective_iff_map_eq_zero _).mpr hj) hc

/-- If `f` is an injective linear map, then the family `f ∘ v` is linearly independent
if and only if the family `v` is linearly independent. -/
/-
**LinearMap.linearIndependent_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {ι : Type u'} {R : Type u_2} {M : Type u_4} {M' : Type u_5} {v : ι → M} 
[inst : Ring R] [inst_1 : AddCommGroup M]   [inst_2 : AddCommGroup M'] [inst_3 :
 _root_.Module R M] [inst_4 : _root_.Module R M'] (f : M →ₗ[R] M'),   f.ker = ⊥ 
→ (LinearIndependent R (⇑f ∘ v) ↔ LinearIndependent R v)
参数：f : M →ₗ[R] M'；LinearIndependent R (⇑f ∘ v) ↔ LinearIndependent R v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.linearIndependent_iff_of_disjoint`：∀ {ι : Type u'} {R : Type u
_2} {M : Type u_4} {M' : Type u_5} [inst : Ring R] [inst_1 : AddCommGroup M]   [
inst_2 : AddCommGroup M'] [inst_3…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
If `f` is an injective linear map, then the family `f ∘ v` is linearly independe
nt
if and only if the family `v` is linearly independent.
-/
protected theorem LinearMap.linearIndependent_iff (f : M →ₗ[R] M') (hf_inj : LinearMap.ker f = ⊥) :
    LinearIndependent R (f ∘ v) ↔ LinearIndependent R v :=
  f.linearIndependent_iff_of_disjoint <| by simp_rw [hf_inj, disjoint_bot_right]

/-- See `LinearIndependent.finCons` for a family of elements in a vector space. -/
/-
**LinearIndependent.finCons'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.finCons' {m : Nat} (x : M) (v : Fin m -> M) (hli : Linea
rIndependent R v) (x_ortho : forall (c : R) (y : M), y in Submodule.span R (Set.
range v) -> c • x + y = 0 -> c = 0) : LinearIndependent R (Fin.cons x v : Fin m.
succ -> M)
参数：x : M；v : Fin m -> M；hli : LinearIndependent R v；x_ortho : forall (c : R) (y 
: M), y in Submodule.span R (Set.range v) -> c • x + y = 0 -> c = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.linearIndependent_iff`：Fintype.linearIndependent_iff [Fintype ι]
 : LinearIndependent R v ↔ forall g : ι -> R, ∑ i, g i • v i = 0 -> forall i, g 
i = 0
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `sum_mem`：∀ {B : Type u_3} {S : B} {M : Type u_4} [inst : AddCommMonoid M
] [inst_1 : SetLike B M] [AddSubmonoidClass B M]   {ι : Type u_5} {t : Finset…
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Fin.cons_succ`：cons_succ : cons x p i.succ = p i
· 使用定理 `Fin.cons_zero`：cons_zero : cons x p 0 = x
· 使用定理 `Fin.sum_univ_succ`：∀ {M : Type u_2} [inst : AddCommMonoid M] {n : ℕ} (f 
: Fin (n + 1) → M), ∑ i, f i = f 0 + ∑ i, f i.succ
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0

--- 原说明 ---
See `LinearIndependent.finCons` for a family of elements in a vector space.
-/
theorem LinearIndependent.finCons' {m : ℕ} (x : M) (v : Fin m → M) (hli : LinearIndependent R v)
    (x_ortho : ∀ (c : R) (y : M), y ∈ Submodule.span R (Set.range v) → c • x + y = 0 → c = 0) :
    LinearIndependent R (Fin.cons x v : Fin m.succ → M) := by
  rw [Fintype.linearIndependent_iff] at hli ⊢
  rintro g total_eq j
  simp_rw [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at total_eq
  have : g 0 = 0 := by
    refine x_ortho (g 0) (∑ i : Fin m, g i.succ • v i) ?_ total_eq
    exact sum_mem fun i _ => smul_mem _ _ (subset_span ⟨i, rfl⟩)
  rw [this, zero_smul, zero_add] at total_eq
  exact Fin.cases this (hli _ total_eq) j

@[deprecated (since := "2026-04-07")]
alias LinearIndependent.fin_cons' := LinearIndependent.finCons'

/-- See `LinearIndependent.finSnoc` for a family of elements in a vector space. -/
/-
**LinearIndependent.finSnoc'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.finSnoc' {m : Nat} (v : Fin m -> M) (x : M) (hli : Linea
rIndependent R v) (x_ortho : forall (c : R) (y : M), y in Submodule.span R (Set.
range v) -> c • x + y = 0 -> c = 0) : LinearIndependent R (Fin.snoc v x : Fin m.
succ -> M)
参数：v : Fin m -> M；x : M；hli : LinearIndependent R v；x_ortho : forall (c : R) (y 
: M), y in Submodule.span R (Set.range v) -> c • x + y = 0 -> c = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.snoc_eq_cons_rotate`：Fin.snoc_eq_cons_rotate {α : Type*} (v : Fin n 
-> α) (a : α) : @Fin.snoc _ (fun _ => α) v a = fun i => @Fin.cons _ (fun _ => α)
 a v (finRota…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `linearIndependent_equiv`：linearIndependent_equiv (e : ι ≃ ι') {f : ι' ->
 M} : LinearIndependent R (f ∘ e) ↔ LinearIndependent R f
· 使用定理 `LinearIndependent.finCons'`：LinearIndependent.finCons' {m : Nat} (x : M)
 (v : Fin m -> M) (hli : LinearIndependent R v) (x_ortho : forall (c : R) (y : M
), y in Submodul…

--- 原说明 ---
See `LinearIndependent.finSnoc` for a family of elements in a vector space.
-/
theorem LinearIndependent.finSnoc' {m : ℕ} (v : Fin m → M) (x : M) (hli : LinearIndependent R v)
    (x_ortho : ∀ (c : R) (y : M), y ∈ Submodule.span R (Set.range v) → c • x + y = 0 → c = 0) :
    LinearIndependent R (Fin.snoc v x : Fin m.succ → M) := by
  rw [Fin.snoc_eq_cons_rotate v x, ← Function.comp_def]
  exact (linearIndependent_equiv _).mpr (.finCons' x v hli x_ortho)

end Module

/-! ### Properties which require `Ring R` -/


section Module

variable {v : ι → M}
variable [Ring R] [AddCommGroup M] [AddCommGroup M']
variable [Module R M] [Module R M']

/-
**linearIndependent_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndependent_sum {v : ι oplus ι' -> M} : LinearIndependent R v ↔ Line
arIndependent R (v ∘ Sum.inl) ∧ LinearIndependent R (v ∘ Sum.inr) ∧ Disjoint (Su
bmodule.span R (range (v ∘ Sum.inl))) (Submodule.span R (range (v ∘ Sum.inr)))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `LinearIndependent.comp`：LinearIndependent.comp (h : LinearIndependent R 
v) (f : ι' -> ι) (hf : Injective f) : LinearIndependent R (v ∘ f)
· 使用定理 `Sum.inl_injective`：inl_injective : Function.Injective (inl : α -> α oplu
s β)
· 使用定理 `Sum.inr_injective`：inr_injective : Function.Injective (inr : β -> α oplu
s β)
· 使用定理 `LinearIndependent.disjoint_span_image`：LinearIndependent.disjoint_span_i
mage (hv : LinearIndependent R v) {s t : Set ι} (hs : Disjoint s t) : Disjoint (
Submodule.span R <| v '' s)…
· 使用定理 `IsCompl.disjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bou
ndedOrder α] {x y : α}, IsCompl x y → Disjoint x y
· 使用定理 `Set.isCompl_range_inl_range_inr`：isCompl_range_inl_range_inr : IsCompl (
range <| @Sum.inl α β) (range Sum.inr)
· 使用定理 `linearIndependent_iff'`：linearIndependent_iff'ₛ : LinearIndependent R v 
↔ forall s : Finset ι, forall f g : ι -> R, ∑ i in s, f i • v i = ∑ i in s, g i 
• v i -> for…
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Finset.sum_preimage'`：∀ {ι : Type u_1} {κ : Type u_2} {β : Type u_3} [in
st : AddCommMonoid β] (f : ι → κ)   [inst_1 : DecidablePred fun x => x ∈ Set.ran
ge f] (s :…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_union`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   Disjoint s₁ s₂ → ∑
 x ∈ s…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.disjoint_filter`：disjoint_filter {s : Finset α} {p q : α -> Prop}
 [DecidablePred p] [DecidablePred q] : Disjoint (s.filter p) (s.filter q) ↔ fora
ll x in s, p…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `Finset.filter_or`：filter_or (s : Finset α) : (s.filter fun a => p a ∨ q 
a) = s.filter p union s.filter q
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.range_inl_union_range_inr`：range_inl_union_range_inr : range (Sum.in
l : α -> α oplus β) union range Sum.inr = univ
· 使用定理 `Finset.filter_true`：∀ {α : Type u_1} {h : DecidablePred fun x => True} (
s : Finset α), {x ∈ s | True} = s
· 使用定理 `Submodule.disjoint_def'`：disjoint_def' {p p' : Submodule R M} : Disjoint
 p p' ↔ forall x in p, forall y in p', x = y -> x = (0 : M)
· 使用定理 `sum_mem`：∀ {B : Type u_3} {S : B} {M : Type u_4} [inst : AddCommMonoid M
] [inst_1 : SetLike B M] [AddSubmonoidClass B M]   {ι : Type u_5} {t : Finset…
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
（共 35 条，此处仅展示前 30 条）
-/
theorem linearIndependent_sum {v : ι ⊕ ι' → M} :
    LinearIndependent R v ↔
      LinearIndependent R (v ∘ Sum.inl) ∧
        LinearIndependent R (v ∘ Sum.inr) ∧
          Disjoint (Submodule.span R (range (v ∘ Sum.inl)))
            (Submodule.span R (range (v ∘ Sum.inr))) := by
  classical
  rw [range_comp v, range_comp v]
  refine ⟨?_, ?_⟩
  · intro h
    refine ⟨h.comp _ Sum.inl_injective, h.comp _ Sum.inr_injective, ?_⟩
    exact h.disjoint_span_image <| isCompl_range_inl_range_inr.disjoint
  rintro ⟨hl, hr, hlr⟩
  rw [linearIndependent_iff'] at *
  intro s g hg i hi
  have :
    ((∑ i ∈ s.preimage Sum.inl Sum.inl_injective.injOn, (fun x => g x • v x) (Sum.inl i)) +
        ∑ i ∈ s.preimage Sum.inr Sum.inr_injective.injOn, (fun x => g x • v x) (Sum.inr i)) =
      0 := by
    -- Porting note: `g` must be specified.
    rw [Finset.sum_preimage' (g := fun x => g x • v x),
      Finset.sum_preimage' (g := fun x => g x • v x), ← Finset.sum_union, ← Finset.filter_or]
    · simpa only [← mem_union, range_inl_union_range_inr, mem_univ, Finset.filter_true]
    · exact Finset.disjoint_filter.2 fun x _ hx =>
        disjoint_left.1 isCompl_range_inl_range_inr.disjoint hx
  rw [← eq_neg_iff_add_eq_zero] at this
  rw [disjoint_def'] at hlr
  have A := by
    refine hlr _ (sum_mem fun i _ => ?_) _ (neg_mem <| sum_mem fun i _ => ?_) this
    · exact smul_mem _ _ (subset_span ⟨Sum.inl i, mem_range_self _, rfl⟩)
    · exact smul_mem _ _ (subset_span ⟨Sum.inr i, mem_range_self _, rfl⟩)
  rcases i with i | i
  · exact hl _ _ A i (Finset.mem_preimage.2 hi)
  · rw [this, neg_eq_zero] at A
    exact hr _ _ A i (Finset.mem_preimage.2 hi)
/-
**LinearIndependent.sum_type** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.sum_type {v' : ι' -> M} (hv : LinearIndependent R v) (hv
' : LinearIndependent R v') (h : Disjoint (Submodule.span R (range v)) (Submodul
e.span R (range v'))) : LinearIndependent R (Sum.elim v v')
参数：hv : LinearIndependent R v；hv' : LinearIndependent R v'；h : Disjoint (Submodu
le.span R (range v)) (Submodule.span R (range v'))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `linearIndependent_sum`：linearIndependent_sum {v : ι oplus ι' -> M} : Lin
earIndependent R v ↔ LinearIndependent R (v ∘ Sum.inl) ∧ LinearIndependent R (v 
∘ Sum.inr) …
-/
theorem LinearIndependent.sum_type {v' : ι' → M} (hv : LinearIndependent R v)
    (hv' : LinearIndependent R v')
    (h : Disjoint (Submodule.span R (range v)) (Submodule.span R (range v'))) :
    LinearIndependent R (Sum.elim v v') :=
  linearIndependent_sum.2 ⟨hv, hv', h⟩
/-
**LinearIndepOn.union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndepOn.union {t : Set ι} (hs : LinearIndepOn R v s) (ht : LinearInd
epOn R v t) (hdj : Disjoint (span R (v '' s)) (span R (v '' t))) : LinearIndepOn
 R v (s union t)
参数：hs : LinearIndepOn R v s；ht : LinearIndepOn R v t；hdj : Disjoint (span R (v '
' s)) (span R (v '' t))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LinearIndependent.sum_type`：LinearIndependent.sum_type {v' : ι' -> M} (h
v : LinearIndependent R v) (hv' : LinearIndependent R v') (h : Disjoint (Submodu
le.span R (range…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_eq_range`：image_eq_range (f : α -> β) (s : Set α) : f '' s = r
ange fun x : s => f x
· 使用定理 `Disjoint.of_image`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {s t : Se
t α}, Disjoint (f '' s) (f '' t) → Disjoint s t
· 使用定理 `Disjoint.of_span₀`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] [
inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, Disjoint
 (Submo…
· 使用定理 `LinearIndepOn.zero_notMem_image`：LinearIndepOn.zero_notMem_image [Nontri
vial R] (hs : LinearIndepOn R v s) : 0 ∉ v '' s
· 使用定理 `LinearIndepOn.eq_1`：∀ {ι : Type u'} (R : Type u_2) {M : Type u_4} (v : ι
 → M) [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R
 M] (s :…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Equiv.Set.union_apply_left`：union_apply_left {α} {s t : Set α} [Decidabl
ePred fun x => x in s] (H : Disjoint s t) {a : (s union t : Set α)} (ha : ↑a in 
s) : Equiv.Set.u…
· 使用定理 `Sum.elim_inl`：∀ {α : Type u_1} {γ : Sort u_2} {β : Type u_3} (f : α → γ)
 (g : β → γ) (x : α), Sum.elim f g (Sum.inl x) = f x
· 使用定理 `Equiv.Set.union_apply_right`：union_apply_right {α} {s t : Set α} [Decida
blePred fun x => x in s] (H : Disjoint s t) {a : (s union t : Set α)} (ha : ↑a i
n t) : Equiv.Set.…
· 使用定理 `Sum.elim_inr`：∀ {α : Type u_1} {γ : Sort u_2} {β : Type u_3} (f : α → γ)
 (g : β → γ) (x : β), Sum.elim f g (Sum.inr x) = g x
· 使用定理 `LinearIndependent.comp`：LinearIndependent.comp (h : LinearIndependent R 
v) (f : ι' -> ι) (hf : Injective f) : LinearIndependent R (v ∘ f)
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
theorem LinearIndepOn.union {t : Set ι} (hs : LinearIndepOn R v s) (ht : LinearIndepOn R v t)
    (hdj : Disjoint (span R (v '' s)) (span R (v '' t))) : LinearIndepOn R v (s ∪ t) := by
  nontriviality R
  classical
  have hli := LinearIndependent.sum_type hs ht (by rwa [← image_eq_range, ← image_eq_range])
  have hdj := (hdj.of_span₀ hs.zero_notMem_image).of_image
  rw [LinearIndepOn]
  convert! (hli.comp _ (Equiv.Set.union hdj).injective) with ⟨x, hx | hx⟩
  · rw [comp_apply, Equiv.Set.union_apply_left _ hx, Sum.elim_inl]
  rw [comp_apply, Equiv.Set.union_apply_right _ hx, Sum.elim_inr]
/-
**LinearIndepOn.id_union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndepOn.id_union {s t : Set M} (hs : LinearIndepOn R id s) (ht : Lin
earIndepOn R id t) (hdj : Disjoint (span R s) (span R t)) : LinearIndepOn R id (
s union t)
参数：hs : LinearIndepOn R id s；ht : LinearIndepOn R id t；hdj : Disjoint (span R s)
 (span R t)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndepOn.union`：LinearIndepOn.union {t : Set ι} (hs : LinearIndepOn
 R v s) (ht : LinearIndepOn R v t) (hdj : Disjoint (span R (v '' s)) (span R (v 
'' t))) :…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
-/
theorem LinearIndepOn.id_union {s t : Set M} (hs : LinearIndepOn R id s) (ht : LinearIndepOn R id t)
    (hdj : Disjoint (span R s) (span R t)) : LinearIndepOn R id (s ∪ t) :=
  hs.union ht (by simpa)
/-
**linearIndepOn_union_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndepOn_union_iff {t : Set ι} (hdj : Disjoint s t) : LinearIndepOn R
 v (s union t) ↔ LinearIndepOn R v s ∧ LinearIndepOn R v t ∧ Disjoint (span R (v
 '' s)) (span R (v '' t))
参数：hdj : Disjoint s t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearIndepOn.mono`：LinearIndepOn.mono {t s : Set ι} (hs : LinearIndepOn
 R v s) (h : t subseteq s) : LinearIndepOn R v t
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `LinearIndependent.disjoint_span_image`：LinearIndependent.disjoint_span_i
mage (hv : LinearIndependent R v) {s t : Set ι} (hs : Disjoint s t) : Disjoint (
Submodule.span R <| v '' s)…
· 使用定理 `Disjoint.preimage`：Disjoint.preimage (f : α -> β) {s t : Set β} (h : Dis
joint s t) : Disjoint (f ⁻¹' s) (f ⁻¹' t)
· 使用定理 `LinearIndepOn.union`：LinearIndepOn.union {t : Set ι} (hs : LinearIndepOn
 R v s) (ht : LinearIndepOn R v t) (hdj : Disjoint (span R (v '' s)) (span R (v 
'' t))) :…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem linearIndepOn_union_iff {t : Set ι} (hdj : Disjoint s t) :
    LinearIndepOn R v (s ∪ t) ↔
    LinearIndepOn R v s ∧ LinearIndepOn R v t ∧ Disjoint (span R (v '' s)) (span R (v '' t)) := by
  refine ⟨fun h ↦ ⟨h.mono subset_union_left, h.mono subset_union_right, ?_⟩,
    fun h ↦ h.1.union h.2.1 h.2.2⟩
  convert! h.disjoint_span_image (s := (↑) ⁻¹' s) (t := (↑) ⁻¹' t) (hdj.preimage _) <;>
  aesop
/-
**linearIndepOn_id_union_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndepOn_id_union_iff {s t : Set M} (hdj : Disjoint s t) : LinearInde
pOn R id (s union t) ↔ LinearIndepOn R id s ∧ LinearIndepOn R id t ∧ Disjoint (s
pan R s) (span R t)
参数：hdj : Disjoint s t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `linearIndepOn_union_iff`：linearIndepOn_union_iff {t : Set ι} (hdj : Disj
oint s t) : LinearIndepOn R v (s union t) ↔ LinearIndepOn R v s ∧ LinearIndepOn 
R v t ∧ Disjo…
· 使用定理 `Set.image_id`：image_id (s : Set α) : id '' s = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem linearIndepOn_id_union_iff {s t : Set M} (hdj : Disjoint s t) :
    LinearIndepOn R id (s ∪ t) ↔
    LinearIndepOn R id s ∧ LinearIndepOn R id t ∧ Disjoint (span R s) (span R t) := by
  rw [linearIndepOn_union_iff hdj, image_id, image_id]

open LinearMap
/-
**LinearIndepOn.image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndepOn.image {s : Set M} {f : M ->ₗ[R] M'} (hs : LinearIndepOn R id
 s) (hf_inj : Disjoint (span R s) (LinearMap.ker f)) : LinearIndepOn R id (f '' 
s)
参数：hs : LinearIndepOn R id s；hf_inj : Disjoint (span R s) (LinearMap.ker f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndepOn.id_imageₛ`：LinearIndepOn.id_imageₛ {s : Set M} {f : M ->ₗ[
R] M'} (hs : LinearIndepOn R id s) (hf_inj : Set.InjOn f (span R s)) : LinearInd
epOn R id (f …
· 使用定理 `LinearMap.injOn_of_disjoint_ker`：injOn_of_disjoint_ker {p : Submodule R 
M} {s : Set M} (h : s subseteq p) (hd : Disjoint p (ker f)) : Set.InjOn f s
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem LinearIndepOn.image {s : Set M} {f : M →ₗ[R] M'}
    (hs : LinearIndepOn R id s) (hf_inj : Disjoint (span R s) (LinearMap.ker f)) :
    LinearIndepOn R id (f '' s) :=
  hs.id_imageₛ <| LinearMap.injOn_of_disjoint_ker le_rfl hf_inj

-- See, for example, Keith Conrad's note [ConradLinearChar]
--  <https://kconrad.math.uconn.edu/blurbs/galoistheory/linearchar.pdf>
/-- Dedekind's linear independence of characters -/
@[stacks 0CKL]
/-
**linearIndependent_monoidHom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndependent_monoidHom (G : Type*) [MulOneClass G] (L : Type*) [CommR
ing L] [IsDomain L] : LinearIndependent L (M
参数：G : Type*；L : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `linearIndependent_iff'`：linearIndependent_iff'ₛ : LinearIndependent R v 
↔ forall s : Finset ι, forall f g : ι -> R, ∑ i in s, f i • v i = ∑ i in s, g i 
• v i -> for…
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `add_sub_add_left_eq_sub`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b c
 : G), c + a - (c + b) = a - b
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
（共 45 条，此处仅展示前 30 条）

--- 原说明 ---
Dedekind's linear independence of characters
-/
theorem linearIndependent_monoidHom (G : Type*) [MulOneClass G] (L : Type*) [CommRing L]
    [IsDomain L] : LinearIndependent L (M := G → L) (fun f => f : (G →* L) → G → L) := by
  let := Classical.decEq (G →* L)
  let : MulAction L L := DistribMulAction.toMulAction
  -- We prove linear independence by showing that only the trivial linear combination vanishes.
  apply linearIndependent_iff'.2
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
  intro g hg
  -- Here
  -- * `a` is a new character we will insert into the `Finset` of characters `s`,
  -- * `ih` is the fact that only the trivial linear combination of characters in `s` is zero
  -- * `hg` is the fact that `g` are the coefficients of a linear combination summing to zero
  -- and it remains to prove that `g` vanishes on `insert a s`.
  -- We now make the key calculation:
  -- For any character `i` in the original `Finset`, we have `g i • i = g i • a` as functions
  -- on the monoid `G`.
  have h1 (i) (his : i ∈ s) : (g i • i : G → L) = g i • a := by
    ext x
    rw [← sub_eq_zero]
    apply ih (fun j => g j * j x - g j * a x) _ i his
    ext y
    -- After that, it's just a chase scene.
    calc
      (∑ i ∈ s, (g i * i x - g i * a x) • i : G → L) y =
          (∑ i ∈ s, g i * i x * i y) - ∑ i ∈ s, g i * a x * i y := by simp [sub_mul]
      _ = (∑ i ∈ insert a s, g i * i x * i y) -
            ∑ i ∈ insert a s, g i * a x * i y := by simp [Finset.sum_insert has]
      _ = (∑ i ∈ insert a s, g i * (i x * i y)) -
            ∑ i ∈ insert a s, a x * (g i * i y) := by
        congrm ∑ i ∈ insert a s, ?_ - ∑ i ∈ insert a s, ?_
        · rw [mul_assoc]
        · rw [mul_assoc, mul_left_comm]
      _ = (∑ i ∈ insert a s, g i • i : G → L) (x * y) -
            a x * (∑ i ∈ insert a s, (g i • (i : G → L))) y := by simp [Finset.mul_sum]
      _ = 0 := by rw [hg]; simp
  -- On the other hand, since `a` is not already in `s`, for any character `i ∈ s`
  -- there is some element of the monoid on which it differs from `a`.
  have h2 (i) (his : i ∈ s) : ∃ y, i y ≠ a y := by
    by_contra! hia
    obtain rfl : i = a := MonoidHom.ext hia
    contradiction
  -- From these two facts we deduce that `g` actually vanishes on `s`,
  have h3 (i) (his : i ∈ s) : g i = 0 := by
    let ⟨y, hy⟩ := h2 i his
    have h : g i • i y = g i • a y := congr_fun (h1 i his) y
    rw [← sub_eq_zero, ← smul_sub, smul_eq_zero] at h
    exact h.resolve_right (sub_ne_zero_of_ne hy)
  -- And so, using the fact that the linear combination over `s` and over `insert a s` both
  -- vanish, we deduce that `g a = 0`.
  have h4 : g a = 0 :=
    calc
      g a = g a * 1 := (mul_one _).symm
      _ = (g a • a : G → L) 1 := by rw [← a.map_one]; rfl
      _ = (∑ i ∈ insert a s, g i • i : G → L) 1 := by
        rw [Finset.sum_insert has, Finset.sum_eq_zero, add_zero]
        simp +contextual [h3]
      _ = 0 := by rw [hg]; rfl
  -- Now we're done; the last two facts together imply that `g` vanishes on every element
  -- of `insert a s`.
  exact (Finset.forall_mem_insert ..).2 ⟨h4, h3⟩

end Module

section IsDomain
variable [Ring R] [IsDomain R] [AddCommGroup M] [Module R M] [Module.IsTorsionFree R M]
  {v : ι → M} {i : ι}

/-
**linearIndependent_unique_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：linearIndependent_unique_iff [Unique ι] : LinearIndependent R v ↔ v defaul
t != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.linearCombination_unique`：linearCombination_unique [Unique α] (l
 : α ->₀ R) (v : α -> M) : linearCombination R v l = l default • v default
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用引理 `LinearIndependent.of_subsingleton`：LinearIndependent.of_subsingleton [Su
bsingleton ι] (i : ι) (hi : v i != 0) : LinearIndependent R v
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
lemma linearIndependent_unique_iff [Unique ι] : LinearIndependent R v ↔ v default ≠ 0 := by
  refine ⟨?_, .of_subsingleton _⟩
  simpa [linearIndependent_iff, Finsupp.linearCombination_unique, Finsupp.ext_iff,
    Unique.forall_iff, or_imp] using fun h hv ↦ by simpa using h (.single default 1) hv

variable (R) in
@[simp]
/-
**linearIndepOn_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndepOn_singleton_iff : LinearIndepOn R v {i} ↔ v i != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndepOn.ne_zero`：LinearIndepOn.ne_zero [Nontrivial R] {i : ι} (hv 
: LinearIndepOn R v s) (hi : i in s) : v i != 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用引理 `LinearIndepOn.singleton`：LinearIndepOn.singleton (hi : v i != 0) : Linea
rIndepOn R v {i}
-/
theorem linearIndepOn_singleton_iff : LinearIndepOn R v {i} ↔ v i ≠ 0 :=
  ⟨fun h ↦ h.ne_zero rfl, .singleton⟩

@[simp]
/-
**linearIndependent_subsingleton_index_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndependent_subsingleton_index_iff [Subsingleton ι] (f : ι -> M) : L
inearIndependent R f ↔ forall i, f i != 0
参数：f : ι -> M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `unique_iff_subsingleton_and_nonempty`：unique_iff_subsingleton_and_nonemp
ty (α : Sort u) : Nonempty (Unique α) ↔ Subsingleton α ∧ Nonempty α
· 使用引理 `linearIndependent_unique_iff`：linearIndependent_unique_iff [Unique ι] : 
LinearIndependent R v ↔ v default != 0
· 使用定理 `Unique.eq_default`：eq_default (a : α) : a = default
-/
theorem linearIndependent_subsingleton_index_iff [Subsingleton ι] (f : ι → M) :
    LinearIndependent R f ↔ ∀ i, f i ≠ 0 := by
  obtain (he | he) := isEmpty_or_nonempty ι
  · simp [linearIndependent_empty_type]
  obtain ⟨_⟩ := (unique_iff_subsingleton_and_nonempty (α := ι)).2 ⟨by assumption, he⟩
  rw [linearIndependent_unique_iff]
  exact ⟨fun h i ↦ by rwa [Unique.eq_default i], fun h ↦ h _⟩

end IsDomain

