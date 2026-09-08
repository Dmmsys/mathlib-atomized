/-
Copyright (c) 2023 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.TensorProduct.Maps

/-! # Right-exactness properties of tensor product

## Modules

* `LinearMap.rTensor_surjective` asserts that when one tensors
  a surjective map on the right, one still gets a surjective linear map.
  More generally, `LinearMap.rTensor_range`  computes the range of
  `LinearMap.rTensor`

* `LinearMap.lTensor_surjective` asserts that when one tensors
  a surjective map on the left, one still gets a surjective linear map.
  More generally, `LinearMap.lTensor_range`  computes the range of
  `LinearMap.lTensor`

* `TensorProduct.rTensor_exact` says that when one tensors a short exact
  sequence on the right, one still gets a short exact sequence
  (right-exactness of `TensorProduct.rTensor`),
  and `rTensor.equiv` gives the LinearEquiv that follows from this
  combined with `LinearMap.rTensor_surjective`.

* `TensorProduct.lTensor_exact` says that when one tensors a short exact
  sequence on the left, one still gets a short exact sequence
  (right-exactness of `TensorProduct.rTensor`)
  and `lTensor.equiv` gives the LinearEquiv that follows from this
  combined with `LinearMap.lTensor_surjective`.

* For `N : Submodule R M`, `LinearMap.exact_subtype_mkQ N` says that
  the inclusion of the submodule and the quotient map form an exact pair,
  and `lTensor_mkQ` compute `ker (lTensor Q (N.mkQ))` and similarly for `rTensor_mkQ`

* `TensorProduct.map_ker` computes the kernel of `TensorProduct.map f g'`
  in the presence of two short exact sequences.

The proofs are those of [bourbaki1989] (chap. 2, §3, n°6)

## Algebras

In the case of a tensor product of algebras, these results can be particularized
to compute some kernels.

* `Algebra.TensorProduct.ker_map` computes the kernel of `Algebra.TensorProduct.map f g`

* `Algebra.TensorProduct.lTensor_ker` and `Algebra.TensorProduct.rTensor_ker`
  compute the kernels of `Algebra.TensorProduct.map f id` and `Algebra.TensorProduct.map id g`

## Note on implementation

* All kernels are computed by applying the first isomorphism theorem and
  establishing some isomorphisms.

* The proofs are essentially done twice,
  once for `lTensor` and then for `rTensor`.
  It is possible to apply `TensorProduct.flip` to deduce one of them
  from the other.
  However, this approach will lead to different isomorphisms,
  and it is not quicker.

* The proofs of `Ideal.map_includeLeft_eq` and `Ideal.map_includeRight_eq`
  could be easier if `I ⊗[R] B` was naturally an `A ⊗[R] B` module,
  and the map to `A ⊗[R] B` was known to be linear.
  This depends on the B-module structure on a tensor product
  whose use rapidly conflicts with everything…

## TODO

* Treat the noncommutative case

* Treat the case of modules over semirings
  (For a possible definition of an exact sequence of commutative semigroups, see
  [Grillet-1969b], Pierre-Antoine Grillet,
  *The tensor product of commutative semigroups*,
  Trans. Amer. Math. Soc. 138 (1969), 281-293, doi:10.1090/S0002-9947-1969-0237688-1 .)

-/

@[expose] public section

assert_not_exists Cardinal

section Modules

open TensorProduct LinearMap

section Semiring

variable {R : Type*} [CommSemiring R] {M N P Q : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q]
    [Module R M] [Module R N] [Module R P] [Module R Q]
    {f : M →ₗ[R] N} (g : N →ₗ[R] P)

/-
**le_comap_range_lTensor** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_comap_range_lTensor (q : Q) : LinearMap.range g <= (LinearMap.range (lT
ensor Q g)).comap (TensorProduct.mk R Q P q)
参数：q : Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma le_comap_range_lTensor (q : Q) :
    LinearMap.range g ≤ (LinearMap.range (lTensor Q g)).comap (TensorProduct.mk R Q P q) := by
  rintro x ⟨n, rfl⟩
  exact ⟨q ⊗ₜ[R] n, rfl⟩
/-
**le_comap_range_rTensor** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_comap_range_rTensor (q : Q) : LinearMap.range g <= (LinearMap.range (rT
ensor Q g)).comap ((TensorProduct.mk R P Q).flip q)
参数：q : Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
-/
lemma le_comap_range_rTensor (q : Q) :
    LinearMap.range g ≤ (LinearMap.range (rTensor Q g)).comap
      ((TensorProduct.mk R P Q).flip q) := by
  rintro x ⟨n, rfl⟩
  exact ⟨n ⊗ₜ[R] q, rfl⟩

variable (Q) {g}

/-- If `g` is surjective, then `lTensor Q g` is surjective -/
/-
**LinearMap.lTensor_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.lTensor_surjective (hg : Function.Surjective g) : Function.Surje
ctive (lTensor Q g)
参数：hg : Function.Surjective g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
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
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…

--- 原说明 ---
If `g` is surjective, then `lTensor Q g` is surjective
-/
theorem LinearMap.lTensor_surjective (hg : Function.Surjective g) :
    Function.Surjective (lTensor Q g) := by
  intro z
  induction z with
  | zero => exact ⟨0, map_zero _⟩
  | tmul q p =>
    obtain ⟨n, rfl⟩ := hg p
    exact ⟨q ⊗ₜ[R] n, rfl⟩
  | add x y hx hy =>
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := hy
    exact ⟨x + y, map_add _ _ _⟩
/-
**LinearMap.lTensor_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.lTensor_range : range (lTensor Q g) = range (lTensor Q (Submodul
e.subtype (range g)))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.lTensor_comp`：lTensor_comp : (g.comp f).lTensor M = (g.lTensor
 M).comp (f.lTensor M)
· 使用定理 `LinearMap.range_comp_of_range_eq_top`：range_comp_of_range_eq_top [RingHo
mSurjective τ₁₂] [RingHomSurjective τ₂₃] [RingHomSurjective τ₁₃] {f : M ->ₛₗ[τ₁₂
] M₂} (g : M₂ ->ₛₗ[τ₂₃] M₃…
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `LinearMap.lTensor_surjective`：LinearMap.lTensor_surjective (hg : Functio
n.Surjective g) : Function.Surjective (lTensor Q g)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.range_rangeRestrict`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Typ
e u_5} {M₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : Ad
dCommMonoid M] [ins…
-/
theorem LinearMap.lTensor_range :
    range (lTensor Q g) =
      range (lTensor Q (Submodule.subtype (range g))) := by
  have : g = (Submodule.subtype _).comp g.rangeRestrict := rfl
  nth_rewrite 1 [this]
  rw [lTensor_comp]
  apply range_comp_of_range_eq_top
  rw [range_eq_top]
  apply lTensor_surjective
  rw [← range_eq_top, range_rangeRestrict]

/-- If `g` is surjective, then `g.baseChange A` is surjective. -/
/-
**LinearMap.baseChange_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.baseChange_surjective (A : Type*) [Semiring A] [Algebra R A] (hg
 : Function.Surjective g) : Function.Surjective (g.baseChange A)
参数：A : Type*；hg : Function.Surjective g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.baseChange_eq_ltensor`：baseChange_eq_ltensor : (f.baseChange A
 : A otimes M -> A otimes N) = f.lTensor A
· 使用定理 `LinearMap.lTensor_surjective`：LinearMap.lTensor_surjective (hg : Functio
n.Surjective g) : Function.Surjective (lTensor Q g)

--- 原说明 ---
If `g` is surjective, then `g.baseChange A` is surjective.
-/
theorem LinearMap.baseChange_surjective (A : Type*) [Semiring A] [Algebra R A]
    (hg : Function.Surjective g) : Function.Surjective (g.baseChange A) := by
  rw [LinearMap.baseChange_eq_ltensor]
  exact lTensor_surjective _ hg

/-- If `g` is surjective, then `rTensor Q g` is surjective -/
/-
**LinearMap.rTensor_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.rTensor_surjective (hg : Function.Surjective g) : Function.Surje
ctive (rTensor Q g)
参数：hg : Function.Surjective g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
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
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…

--- 原说明 ---
If `g` is surjective, then `rTensor Q g` is surjective
-/
theorem LinearMap.rTensor_surjective (hg : Function.Surjective g) :
    Function.Surjective (rTensor Q g) := by
  intro z
  induction z with
  | zero => exact ⟨0, map_zero _⟩
  | tmul p q =>
    obtain ⟨n, rfl⟩ := hg p
    exact ⟨n ⊗ₜ[R] q, rfl⟩
  | add x y hx hy =>
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := hy
    exact ⟨x + y, map_add _ _ _⟩
/-
**LinearMap.rTensor_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.rTensor_range : range (rTensor Q g) = range (rTensor Q (Submodul
e.subtype (range g)))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.rTensor_comp`：rTensor_comp : (g.comp f).rTensor M = (g.rTensor
 M).comp (f.rTensor M)
· 使用定理 `LinearMap.range_comp_of_range_eq_top`：range_comp_of_range_eq_top [RingHo
mSurjective τ₁₂] [RingHomSurjective τ₂₃] [RingHomSurjective τ₁₃] {f : M ->ₛₗ[τ₁₂
] M₂} (g : M₂ ->ₛₗ[τ₂₃] M₃…
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `LinearMap.rTensor_surjective`：LinearMap.rTensor_surjective (hg : Functio
n.Surjective g) : Function.Surjective (rTensor Q g)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.range_rangeRestrict`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Typ
e u_5} {M₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : Ad
dCommMonoid M] [ins…
-/
theorem LinearMap.rTensor_range :
    range (rTensor Q g) =
      range (rTensor Q (Submodule.subtype (range g))) := by
  have : g = (Submodule.subtype _).comp g.rangeRestrict := rfl
  nth_rewrite 1 [this]
  rw [rTensor_comp]
  apply range_comp_of_range_eq_top
  rw [range_eq_top]
  apply rTensor_surjective
  rw [← range_eq_top, range_rangeRestrict]
/-
**LinearMap.rTensor_exact_iff_lTensor_exact** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearMap.rTensor_exact_iff_lTensor_exact : Function.Exact (f.rTensor Q) (
g.rTensor Q) ↔ Function.Exact (f.lTensor Q) (g.lTensor Q)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.Exact.iff_of_ladder_linearEquiv`：iff_of_ladder_linearEquiv (h₁₂
 : g₁₂ ∘ₗ e₁ = e₂ ∘ₗ f₁₂) (h₂₃ : g₂₃ ∘ₗ e₂ = e₃ ∘ₗ f₂₃) : Exact g₁₂ g₂₃ ↔ Exact 
f₁₂ f₂₃
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
-/
lemma LinearMap.rTensor_exact_iff_lTensor_exact :
    Function.Exact (f.rTensor Q) (g.rTensor Q) ↔
    Function.Exact (f.lTensor Q) (g.lTensor Q) :=
  Function.Exact.iff_of_ladder_linearEquiv (e₁ := TensorProduct.comm _ _ _)
    (e₂ := TensorProduct.comm _ _ _) (e₃ := TensorProduct.comm _ _ _)
    (by ext; simp) (by ext; simp)

variable (hg : Function.Surjective g)
    {N' P' : Type*} [AddCommMonoid N'] [AddCommMonoid P'] [Module R N'] [Module R P']
    {g' : N' →ₗ[R] P'} (hg' : Function.Surjective g')

include hg hg' in
/-
**TensorProduct.map_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TensorProduct.map_surjective : Function.Surjective (TensorProduct.map g g'
)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.lTensor_comp_rTensor`：lTensor_comp_rTensor (f : M ->ₗ[R] P) (g
 : N ->ₗ[R] Q) : (g.lTensor P).comp (f.rTensor N) = map f g
· 使用定理 `LinearMap.coe_comp`：coe_comp : (f.comp g : M₁ -> M₃) = f ∘ g
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `LinearMap.lTensor_surjective`：LinearMap.lTensor_surjective (hg : Functio
n.Surjective g) : Function.Surjective (lTensor Q g)
· 使用定理 `LinearMap.rTensor_surjective`：LinearMap.rTensor_surjective (hg : Functio
n.Surjective g) : Function.Surjective (rTensor Q g)
-/
theorem TensorProduct.map_surjective : Function.Surjective (TensorProduct.map g g') := by
  rw [← lTensor_comp_rTensor, coe_comp]
  exact Function.Surjective.comp (lTensor_surjective _ hg') (rTensor_surjective _ hg)

end Semiring

variable {R M N P : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]

open Function

variable {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (Q : Type*) [AddCommGroup Q] [Module R Q]
    (hfg : Exact f g) (hg : Function.Surjective g)

/-- The direct map in `lTensor.equiv` -/
/-
**lTensor.toFun** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：lTensor.toFun (hfg : Exact f g) : Q otimes[R] N ⧸ LinearMap.range (lTensor
 Q f) ->ₗ[R] Q otimes[R] P
参数：hfg : Exact f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The direct map in `lTensor.equiv`
-/
noncomputable def lTensor.toFun (hfg : Exact f g) :
    Q ⊗[R] N ⧸ LinearMap.range (lTensor Q f) →ₗ[R] Q ⊗[R] P :=
  Submodule.liftQ _ (lTensor Q g) <| by
    rw [LinearMap.range_le_iff_comap, ← LinearMap.ker_comp,
      ← lTensor_comp, hfg.linearMap_comp_eq_zero, lTensor_zero, ker_zero]

set_option backward.isDefEq.respectTransparency false in
/-- The inverse map in `lTensor.equiv_of_rightInverse` (computably, given a right inverse) -/
/-
**lTensor.inverse_of_rightInverse** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：lTensor.inverse_of_rightInverse {h : P -> N} (hfg : Exact f g) (hgh : Func
tion.RightInverse h g) : Q otimes[R] P ->ₗ[R] Q otimes[R] N ⧸ LinearMap.range (l
Tensor Q f)
参数：hfg : Exact f g；hgh : Function.RightInverse h g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse map in `lTensor.equiv_of_rightInverse` (computably, given a right in
verse)
-/
noncomputable def lTensor.inverse_of_rightInverse {h : P → N} (hfg : Exact f g)
    (hgh : Function.RightInverse h g) :
    Q ⊗[R] P →ₗ[R] Q ⊗[R] N ⧸ LinearMap.range (lTensor Q f) :=
  TensorProduct.lift <| LinearMap.flip <| {
    toFun := fun p ↦ Submodule.mkQ _ ∘ₗ ((TensorProduct.mk R _ _).flip (h p))
    map_add' := fun p p' => LinearMap.ext fun q => (Submodule.Quotient.eq _).mpr <| by
      change q ⊗ₜ[R] (h (p + p')) - (q ⊗ₜ[R] (h p) + q ⊗ₜ[R] (h p')) ∈ range (lTensor Q f)
      rw [← TensorProduct.tmul_add, ← TensorProduct.tmul_sub]
      apply le_comap_range_lTensor f
      rw [exact_iff] at hfg
      simp only [← hfg, mem_ker, map_sub, map_add, hgh _, sub_self]
    map_smul' := fun r p => LinearMap.ext fun q => (Submodule.Quotient.eq _).mpr <| by
      change q ⊗ₜ[R] (h (r • p)) - r • q ⊗ₜ[R] (h p) ∈ range (lTensor Q f)
      rw [← TensorProduct.tmul_smul, ← TensorProduct.tmul_sub]
      apply le_comap_range_lTensor f
      rw [exact_iff] at hfg
      simp only [← hfg, mem_ker, map_sub, map_smul, hgh _, sub_self] }
/-
**lTensor.inverse_of_rightInverse_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lTensor.inverse_of_rightInverse_apply {h : P -> N} (hgh : Function.RightIn
verse h g) (y : Q otimes[R] N) : (lTensor.inverse_of_rightInverse Q hfg hgh) ((l
Tensor Q g) y) = Submodule.Quotient.mk (p
参数：hgh : Function.RightInverse h g；y : Q otimes[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用定理 `TensorProduct.ext'`：ext' {g h : M otimes[R] N ->ₛₗ[σ₁₂] P₂} (H : forall 
x y, g (x otimesₜ y) = h (x otimesₜ y)) : g = h
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.Quotient.eq`：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] [
inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (p : Submodule R M) {x y
 : M}, Subm…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TensorProduct.tmul_sub`：tmul_sub (m : M) (p₁ p₂ : P) : m otimesₜ (p₁ - p
₂) = m otimesₜ[R] p₁ - m otimesₜ[R] p₂
· 使用引理 `le_comap_range_lTensor`：le_comap_range_lTensor (q : Q) : LinearMap.range
 g <= (LinearMap.range (lTensor Q g)).comap (TensorProduct.mk R Q P q)
· 使用引理 `LinearMap.exact_iff`：exact_iff : Exact f g ↔ LinearMap.ker g = LinearMap
.range f
· 使用定理 `LinearMap.mem_ker`：mem_ker {f : M ->ₛₗ[τ₁₂] M₂} {y} : y in ker f ↔ f y =
 0
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
-/
lemma lTensor.inverse_of_rightInverse_apply
    {h : P → N} (hgh : Function.RightInverse h g) (y : Q ⊗[R] N) :
    (lTensor.inverse_of_rightInverse Q hfg hgh) ((lTensor Q g) y) =
      Submodule.Quotient.mk (p := (LinearMap.range (lTensor Q f))) y := by
  simp only [← LinearMap.comp_apply, ← Submodule.mkQ_apply]
  rw [exact_iff] at hfg
  apply LinearMap.congr_fun
  apply TensorProduct.ext'
  intro n q
  suffices Submodule.Quotient.mk (n ⊗ₜ[R] h (g q)) = Submodule.Quotient.mk (n ⊗ₜ[R] q) by
    simpa
  rw [Submodule.Quotient.eq, ← TensorProduct.tmul_sub]
  apply le_comap_range_lTensor f n
  rw [← hfg, mem_ker, map_sub, sub_eq_zero, hgh]
/-
**lTensor.inverse_of_rightInverse_comp_lTensor** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lTensor.inverse_of_rightInverse_comp_lTensor {h : P -> N} (hgh : Function.
RightInverse h g) : (lTensor.inverse_of_rightInverse Q hfg hgh).comp (lTensor Q 
g) = Submodule.mkQ (p
参数：hgh : Function.RightInverse h g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.ext_iff`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `lTensor.inverse_of_rightInverse_apply`：lTensor.inverse_of_rightInverse_a
pply {h : P -> N} (hgh : Function.RightInverse h g) (y : Q otimes[R] N) : (lTens
or.inverse_of_rightInverse …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lTensor.inverse_of_rightInverse_comp_lTensor
    {h : P → N} (hgh : Function.RightInverse h g) :
    (lTensor.inverse_of_rightInverse Q hfg hgh).comp (lTensor Q g) =
      Submodule.mkQ (p := LinearMap.range (lTensor Q f)) := by
  rw [LinearMap.ext_iff]
  intro y
  simp only [coe_comp, Function.comp_apply, Submodule.mkQ_apply,
    lTensor.inverse_of_rightInverse_apply]

/-- The inverse map in `lTensor.equiv` -/
noncomputable
/-
**lTensor.inverse** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：lTensor.inverse : Q otimes[R] P ->ₗ[R] Q otimes[R] N ⧸ LinearMap.range (lT
ensor Q f)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def lTensor.inverse :
    Q ⊗[R] P →ₗ[R] Q ⊗[R] N ⧸ LinearMap.range (lTensor Q f) :=
  lTensor.inverse_of_rightInverse Q hfg (Function.rightInverse_surjInv hg)
/-
**lTensor.inverse_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lTensor.inverse_apply (y : Q otimes[R] N) : (lTensor.inverse Q hfg hg) ((l
Tensor Q g) y) = Submodule.Quotient.mk (p
参数：y : Q otimes[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lTensor.inverse.eq_1`：∀ {R : Type u_1} {M : Type u_2} {N : Type u_3} {P 
: Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : AddCommGro
up N] [ins…
· 使用引理 `lTensor.inverse_of_rightInverse_apply`：lTensor.inverse_of_rightInverse_a
pply {h : P -> N} (hgh : Function.RightInverse h g) (y : Q otimes[R] N) : (lTens
or.inverse_of_rightInverse …
-/
lemma lTensor.inverse_apply (y : Q ⊗[R] N) :
    (lTensor.inverse Q hfg hg) ((lTensor Q g) y) =
      Submodule.Quotient.mk (p := (LinearMap.range (lTensor Q f))) y := by
  rw [lTensor.inverse, lTensor.inverse_of_rightInverse_apply]
/-
**lTensor.inverse_comp_lTensor** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lTensor.inverse_comp_lTensor : (lTensor.inverse Q hfg hg).comp (lTensor Q 
g) = Submodule.mkQ (p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lTensor.inverse.eq_1`：∀ {R : Type u_1} {M : Type u_2} {N : Type u_3} {P 
: Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : AddCommGro
up N] [ins…
· 使用引理 `lTensor.inverse_of_rightInverse_comp_lTensor`：lTensor.inverse_of_rightIn
verse_comp_lTensor {h : P -> N} (hgh : Function.RightInverse h g) : (lTensor.inv
erse_of_rightInverse Q hfg hgh).co…
-/
lemma lTensor.inverse_comp_lTensor :
    (lTensor.inverse Q hfg hg).comp (lTensor Q g) =
      Submodule.mkQ (p := LinearMap.range (lTensor Q f)) := by
  rw [lTensor.inverse, lTensor.inverse_of_rightInverse_comp_lTensor]

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- For a surjective `f : N →ₗ[R] P`,
  the natural equivalence between `Q ⊗ N ⧸ (image of ker f)` to `Q ⊗ P`
  (computably, given a right inverse) -/
noncomputable
/-
**lTensor.linearEquiv_of_rightInverse** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：lTensor.linearEquiv_of_rightInverse {h : P -> N} (hgh : Function.RightInve
rse h g) : ((Q otimes[R] N) ⧸ (LinearMap.range (lTensor Q f))) ≃ₗ[R] (Q otimes[R
] P)
参数：hgh : Function.RightInverse h g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def lTensor.linearEquiv_of_rightInverse {h : P → N} (hgh : Function.RightInverse h g) :
    ((Q ⊗[R] N) ⧸ (LinearMap.range (lTensor Q f))) ≃ₗ[R] (Q ⊗[R] P) := {
  toLinearMap := lTensor.toFun Q hfg
  invFun   := lTensor.inverse_of_rightInverse Q hfg hgh
  left_inv := fun y ↦ by
    simp only [lTensor.toFun, AddHom.toFun_eq_coe, coe_toAddHom]
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
    simp only [Submodule.mkQ_apply, Submodule.liftQ_apply, lTensor.inverse_of_rightInverse_apply]
  right_inv := fun z ↦ by
    simp only [AddHom.toFun_eq_coe, coe_toAddHom]
    obtain ⟨y, rfl⟩ := lTensor_surjective Q (hgh.surjective) z
    rw [lTensor.inverse_of_rightInverse_apply]
    simp only [lTensor.toFun, Submodule.liftQ_apply] }

/-- For a surjective `f : N →ₗ[R] P`,
  the natural equivalence between `Q ⊗ N ⧸ (image of ker f)` to `Q ⊗ P` -/
/-
**lTensor.equiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：lTensor.equiv : ((Q otimes[R] N) ⧸ (LinearMap.range (lTensor Q f))) ≃ₗ[R] 
(Q otimes[R] P)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a surjective `f : N →ₗ[R] P`,
  the natural equivalence between `Q ⊗ N ⧸ (image of ker f)` to `Q ⊗ P`
-/
noncomputable def lTensor.equiv :
    ((Q ⊗[R] N) ⧸ (LinearMap.range (lTensor Q f))) ≃ₗ[R] (Q ⊗[R] P) :=
  lTensor.linearEquiv_of_rightInverse Q hfg (Function.rightInverse_surjInv hg)

include hfg hg in
/-- Tensoring an exact pair on the left gives an exact pair -/
/-
**lTensor_exact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lTensor_exact : Exact (lTensor Q f) (lTensor Q g)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearMap.exact_iff`：exact_iff : Exact f g ↔ LinearMap.ker g = LinearMap
.range f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.ker_mkQ`：ker_mkQ : ker p.mkQ = p
· 使用引理 `lTensor.inverse_comp_lTensor`：lTensor.inverse_comp_lTensor : (lTensor.in
verse Q hfg hg).comp (lTensor Q g) = Submodule.mkQ (p
· 使用引理 `symm`：symm [Std.Symm r] : a ≺ b -> b ≺ a
· 使用定理 `IsEquiv.toSymm`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEquiv α r]
, Std.Symm r
· 使用定理 `LinearMap.ker_comp_of_ker_eq_bot`：ker_comp_of_ker_eq_bot (f : M ->ₛₗ[τ₁₂
] M₂) {g : M₂ ->ₛₗ[τ₂₃] M₃} (hg : ker g = ⊥) : ker (g.comp f : M ->ₛₗ[τ₁₃] M₃) =
 ker f
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…

--- 原说明 ---
Tensoring an exact pair on the left gives an exact pair
-/
theorem lTensor_exact : Exact (lTensor Q f) (lTensor Q g) := by
  rw [exact_iff, ← Submodule.ker_mkQ (p := range (lTensor Q f)),
    ← lTensor.inverse_comp_lTensor Q hfg hg]
  apply symm
  apply LinearMap.ker_comp_of_ker_eq_bot
  rw [LinearMap.ker_eq_bot]
  exact (lTensor.equiv Q hfg hg).symm.injective

/-- Right-exactness of tensor product -/
/-
**lTensor_mkQ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lTensor_mkQ (N : Submodule R M) : ker (lTensor Q N.mkQ) = range (lTensor Q
 N.subtype)
参数：N : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LinearMap.exact_iff`：exact_iff : Exact f g ↔ LinearMap.ker g = LinearMap
.range f
· 使用定理 `lTensor_exact`：lTensor_exact : Exact (lTensor Q f) (lTensor Q g)
· 使用引理 `LinearMap.exact_subtype_mkQ`：exact_subtype_mkQ (Q : Submodule R N) : Exa
ct (Submodule.subtype Q) (Submodule.mkQ Q)
· 使用定理 `Submodule.mkQ_surjective`：mkQ_surjective : Function.Surjective p.mkQ

--- 原说明 ---
Right-exactness of tensor product
-/
lemma lTensor_mkQ (N : Submodule R M) :
    ker (lTensor Q N.mkQ) = range (lTensor Q N.subtype) := by
  rw [← exact_iff]
  exact lTensor_exact Q (LinearMap.exact_subtype_mkQ N) (Submodule.mkQ_surjective N)

/-- The direct map in `rTensor.equiv` -/
/-
**rTensor.toFun** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：rTensor.toFun (hfg : Exact f g) : N otimes[R] Q ⧸ range (rTensor Q f) ->ₗ[
R] P otimes[R] Q
参数：hfg : Exact f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The direct map in `rTensor.equiv`
-/
noncomputable def rTensor.toFun (hfg : Exact f g) :
    N ⊗[R] Q ⧸ range (rTensor Q f) →ₗ[R] P ⊗[R] Q :=
  Submodule.liftQ _ (rTensor Q g) <| by
    rw [range_le_iff_comap, ← ker_comp, ← rTensor_comp,
      hfg.linearMap_comp_eq_zero, rTensor_zero, ker_zero]

set_option backward.isDefEq.respectTransparency false in
/-- The inverse map in `rTensor.equiv_of_rightInverse` (computably, given a right inverse) -/
/-
**rTensor.inverse_of_rightInverse** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：rTensor.inverse_of_rightInverse {h : P -> N} (hfg : Exact f g) (hgh : Func
tion.RightInverse h g) : P otimes[R] Q ->ₗ[R] N otimes[R] Q ⧸ LinearMap.range (r
Tensor Q f)
参数：hfg : Exact f g；hgh : Function.RightInverse h g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse map in `rTensor.equiv_of_rightInverse` (computably, given a right in
verse)
-/
noncomputable def rTensor.inverse_of_rightInverse {h : P → N} (hfg : Exact f g)
    (hgh : Function.RightInverse h g) :
    P ⊗[R] Q →ₗ[R] N ⊗[R] Q ⧸ LinearMap.range (rTensor Q f) :=
  TensorProduct.lift {
    toFun := fun p ↦ Submodule.mkQ _ ∘ₗ TensorProduct.mk R _ _ (h p)
    map_add' := fun p p' => LinearMap.ext fun q => (Submodule.Quotient.eq _).mpr <| by
      change h (p + p') ⊗ₜ[R] q - (h p ⊗ₜ[R] q + h p' ⊗ₜ[R] q) ∈ range (rTensor Q f)
      rw [← TensorProduct.add_tmul, ← TensorProduct.sub_tmul]
      apply le_comap_range_rTensor f
      rw [exact_iff] at hfg
      simp only [← hfg, mem_ker, map_sub, map_add, hgh _, sub_self]
    map_smul' := fun r p => LinearMap.ext fun q => (Submodule.Quotient.eq _).mpr <| by
      change h (r • p) ⊗ₜ[R] q - r • h p ⊗ₜ[R] q ∈ range (rTensor Q f)
      rw [TensorProduct.smul_tmul', ← TensorProduct.sub_tmul]
      apply le_comap_range_rTensor f
      rw [exact_iff] at hfg
      simp only [← hfg, mem_ker, map_sub, map_smul, hgh _, sub_self] }
/-
**rTensor.inverse_of_rightInverse_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：rTensor.inverse_of_rightInverse_apply {h : P -> N} (hgh : Function.RightIn
verse h g) (y : N otimes[R] Q) : (rTensor.inverse_of_rightInverse Q hfg hgh) ((r
Tensor Q g) y) = Submodule.Quotient.mk (p
参数：hgh : Function.RightInverse h g；y : N otimes[R] Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用定理 `TensorProduct.ext'`：ext' {g h : M otimes[R] N ->ₛₗ[σ₁₂] P₂} (H : forall 
x y, g (x otimesₜ y) = h (x otimesₜ y)) : g = h
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.Quotient.eq`：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] [
inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (p : Submodule R M) {x y
 : M}, Subm…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TensorProduct.sub_tmul`：sub_tmul (m₁ m₂ : M) (n : N) : (m₁ - m₂) otimesₜ
 n = m₁ otimesₜ[R] n - m₂ otimesₜ[R] n
· 使用引理 `le_comap_range_rTensor`：le_comap_range_rTensor (q : Q) : LinearMap.range
 g <= (LinearMap.range (rTensor Q g)).comap ((TensorProduct.mk R P Q).flip q)
· 使用引理 `LinearMap.exact_iff`：exact_iff : Exact f g ↔ LinearMap.ker g = LinearMap
.range f
· 使用定理 `LinearMap.mem_ker`：mem_ker {f : M ->ₛₗ[τ₁₂] M₂} {y} : y in ker f ↔ f y =
 0
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
-/
lemma rTensor.inverse_of_rightInverse_apply
    {h : P → N} (hgh : Function.RightInverse h g) (y : N ⊗[R] Q) :
    (rTensor.inverse_of_rightInverse Q hfg hgh) ((rTensor Q g) y) =
      Submodule.Quotient.mk (p := LinearMap.range (rTensor Q f)) y := by
  simp only [← LinearMap.comp_apply, ← Submodule.mkQ_apply]
  rw [exact_iff] at hfg
  apply LinearMap.congr_fun
  apply TensorProduct.ext'
  intro n q
  suffices Submodule.Quotient.mk (h (g n) ⊗ₜ[R] q) = Submodule.Quotient.mk (n ⊗ₜ[R] q) by simpa
  rw [Submodule.Quotient.eq, ← TensorProduct.sub_tmul]
  apply le_comap_range_rTensor f
  rw [← hfg, mem_ker, map_sub, sub_eq_zero, hgh]
/-
**rTensor.inverse_of_rightInverse_comp_rTensor** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：rTensor.inverse_of_rightInverse_comp_rTensor {h : P -> N} (hgh : Function.
RightInverse h g) : (rTensor.inverse_of_rightInverse Q hfg hgh).comp (rTensor Q 
g) = Submodule.mkQ (p
参数：hgh : Function.RightInverse h g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.ext_iff`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `rTensor.inverse_of_rightInverse_apply`：rTensor.inverse_of_rightInverse_a
pply {h : P -> N} (hgh : Function.RightInverse h g) (y : N otimes[R] Q) : (rTens
or.inverse_of_rightInverse …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rTensor.inverse_of_rightInverse_comp_rTensor
    {h : P → N} (hgh : Function.RightInverse h g) :
    (rTensor.inverse_of_rightInverse Q hfg hgh).comp (rTensor Q g) =
      Submodule.mkQ (p := LinearMap.range (rTensor Q f)) := by
  rw [LinearMap.ext_iff]
  intro y
  simp only [coe_comp, Function.comp_apply, Submodule.mkQ_apply,
    rTensor.inverse_of_rightInverse_apply]

/-- The inverse map in `rTensor.equiv` -/
noncomputable
/-
**rTensor.inverse** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：rTensor.inverse : P otimes[R] Q ->ₗ[R] N otimes[R] Q ⧸ LinearMap.range (rT
ensor Q f)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def rTensor.inverse :
    P ⊗[R] Q →ₗ[R] N ⊗[R] Q ⧸ LinearMap.range (rTensor Q f) :=
  rTensor.inverse_of_rightInverse Q hfg (Function.rightInverse_surjInv hg)
/-
**rTensor.inverse_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：rTensor.inverse_apply (y : N otimes[R] Q) : (rTensor.inverse Q hfg hg) ((r
Tensor Q g) y) = Submodule.Quotient.mk (p
参数：y : N otimes[R] Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rTensor.inverse.eq_1`：∀ {R : Type u_1} {M : Type u_2} {N : Type u_3} {P 
: Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : AddCommGro
up N] [ins…
· 使用引理 `rTensor.inverse_of_rightInverse_apply`：rTensor.inverse_of_rightInverse_a
pply {h : P -> N} (hgh : Function.RightInverse h g) (y : N otimes[R] Q) : (rTens
or.inverse_of_rightInverse …
-/
lemma rTensor.inverse_apply (y : N ⊗[R] Q) :
    (rTensor.inverse Q hfg hg) ((rTensor Q g) y) =
      Submodule.Quotient.mk (p := LinearMap.range (rTensor Q f)) y := by
  rw [rTensor.inverse, rTensor.inverse_of_rightInverse_apply]
/-
**rTensor.inverse_comp_rTensor** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：rTensor.inverse_comp_rTensor : (rTensor.inverse Q hfg hg).comp (rTensor Q 
g) = Submodule.mkQ (p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rTensor.inverse.eq_1`：∀ {R : Type u_1} {M : Type u_2} {N : Type u_3} {P 
: Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : AddCommGro
up N] [ins…
· 使用引理 `rTensor.inverse_of_rightInverse_comp_rTensor`：rTensor.inverse_of_rightIn
verse_comp_rTensor {h : P -> N} (hgh : Function.RightInverse h g) : (rTensor.inv
erse_of_rightInverse Q hfg hgh).co…
-/
lemma rTensor.inverse_comp_rTensor :
    (rTensor.inverse Q hfg hg).comp (rTensor Q g) =
      Submodule.mkQ (p := LinearMap.range (rTensor Q f)) := by
  rw [rTensor.inverse, rTensor.inverse_of_rightInverse_comp_rTensor]

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- For a surjective `f : N →ₗ[R] P`,
  the natural equivalence between `N ⊗[R] Q ⧸ (range (rTensor Q f))` and `P ⊗[R] Q`
  (computably, given a right inverse) -/
noncomputable
/-
**rTensor.linearEquiv_of_rightInverse** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：rTensor.linearEquiv_of_rightInverse {h : P -> N} (hgh : Function.RightInve
rse h g) : ((N otimes[R] Q) ⧸ (range (rTensor Q f))) ≃ₗ[R] (P otimes[R] Q)
参数：hgh : Function.RightInverse h g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def rTensor.linearEquiv_of_rightInverse {h : P → N} (hgh : Function.RightInverse h g) :
    ((N ⊗[R] Q) ⧸ (range (rTensor Q f))) ≃ₗ[R] (P ⊗[R] Q) := {
  toLinearMap := rTensor.toFun Q hfg
  invFun      := rTensor.inverse_of_rightInverse Q hfg hgh
  left_inv    := fun y ↦ by
    simp only [rTensor.toFun, AddHom.toFun_eq_coe, coe_toAddHom]
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
    simp only [Submodule.mkQ_apply, Submodule.liftQ_apply, rTensor.inverse_of_rightInverse_apply]
  right_inv   := fun z ↦ by
    simp only [AddHom.toFun_eq_coe, coe_toAddHom]
    obtain ⟨y, rfl⟩ := rTensor_surjective Q hgh.surjective z
    rw [rTensor.inverse_of_rightInverse_apply]
    simp only [rTensor.toFun, Submodule.liftQ_apply] }

/-- For a surjective `f : N →ₗ[R] P`,
  the natural equivalence between `N ⊗[R] Q ⧸ (range (rTensor Q f))` and `P ⊗[R] Q` -/
/-
**rTensor.equiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：rTensor.equiv : ((N otimes[R] Q) ⧸ (LinearMap.range (rTensor Q f))) ≃ₗ[R] 
(P otimes[R] Q)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a surjective `f : N →ₗ[R] P`,
  the natural equivalence between `N ⊗[R] Q ⧸ (range (rTensor Q f))` and `P ⊗[R]
 Q`
-/
noncomputable def rTensor.equiv :
    ((N ⊗[R] Q) ⧸ (LinearMap.range (rTensor Q f))) ≃ₗ[R] (P ⊗[R] Q) :=
  rTensor.linearEquiv_of_rightInverse Q hfg (Function.rightInverse_surjInv hg)

include hfg hg in
/-- Tensoring an exact pair on the right gives an exact pair -/
/-
**rTensor_exact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rTensor_exact : Exact (rTensor Q f) (rTensor Q g)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearMap.rTensor_exact_iff_lTensor_exact`：LinearMap.rTensor_exact_iff_l
Tensor_exact : Function.Exact (f.rTensor Q) (g.rTensor Q) ↔ Function.Exact (f.lT
ensor Q) (g.lTensor Q)
· 使用定理 `lTensor_exact`：lTensor_exact : Exact (lTensor Q f) (lTensor Q g)

--- 原说明 ---
Tensoring an exact pair on the right gives an exact pair
-/
theorem rTensor_exact : Exact (rTensor Q f) (rTensor Q g) := by
  rw [rTensor_exact_iff_lTensor_exact]
  exact lTensor_exact Q hfg hg

/-- Right-exactness of tensor product (`rTensor`) -/
/-
**rTensor_mkQ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：rTensor_mkQ (N : Submodule R M) : ker (rTensor Q N.mkQ) = range (rTensor Q
 N.subtype)
参数：N : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LinearMap.exact_iff`：exact_iff : Exact f g ↔ LinearMap.ker g = LinearMap
.range f
· 使用定理 `rTensor_exact`：rTensor_exact : Exact (rTensor Q f) (rTensor Q g)
· 使用引理 `LinearMap.exact_subtype_mkQ`：exact_subtype_mkQ (Q : Submodule R N) : Exa
ct (Submodule.subtype Q) (Submodule.mkQ Q)
· 使用定理 `Submodule.mkQ_surjective`：mkQ_surjective : Function.Surjective p.mkQ

--- 原说明 ---
Right-exactness of tensor product (`rTensor`)
-/
lemma rTensor_mkQ (N : Submodule R M) :
    ker (rTensor Q N.mkQ) = range (rTensor Q N.subtype) := by
  rw [← exact_iff]
  exact rTensor_exact Q (LinearMap.exact_subtype_mkQ N) (Submodule.mkQ_surjective N)

open Submodule LinearEquiv in
/-
**LinearMap.ker_tensorProductMk** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearMap.ker_tensorProductMk {I : Ideal R} : ker (TensorProduct.mk R (R ⧸
 I) Q 1) = I • ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.comap_injective_of_surjective`：comap_injective_of_surjective :
 Function.Injective (comap f)
· 使用定理 `LinearEquiv.surjective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {
M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMono
id M] [inst_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.ker_comp`：ker_comp (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) 
: ker (g.comp f : M ->ₛₗ[τ₁₃] M₃) = comap f (ker g)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `Submodule.comap_equiv_eq_map_symm`：comap_equiv_eq_map_symm (e : M ≃ₛₗ[τ₁
₂] M₂) (K : Submodule R₂ M₂) : K.comap (e : M ->ₛₗ[τ₁₂] M₂) = K.map (e.symm : M₂
 ->ₛₗ[τ₂₁] M)
· 使用定理 `Submodule.map_symm_eq_iff`：map_symm_eq_iff (e : M ≃ₛₗ[τ₁₂] M₂) {K : Subm
odule R₂ M₂} : K.map (e.symm : M₂ ->ₛₗ[τ₂₁] M) = p ↔ p.map (e : M ->ₛₗ[τ₁₂] M₂) 
= K
· 使用引理 `Submodule.map_range_rTensor_subtype_lid`：Submodule.map_range_rTensor_sub
type_lid {R Q} [CommSemiring R] [AddCommMonoid Q] [Module R Q] {I : Submodule R 
R} : (range <| rTensor Q I.su…
· 使用引理 `rTensor_mkQ`：rTensor_mkQ (N : Submodule R M) : ker (rTensor Q N.mkQ) = r
ange (rTensor Q N.subtype)
-/
lemma LinearMap.ker_tensorProductMk {I : Ideal R} :
    ker (TensorProduct.mk R (R ⧸ I) Q 1) = I • ⊤ := by
  apply comap_injective_of_surjective (TensorProduct.lid R Q).surjective
  rw [← ker_comp]
  convert! rTensor_mkQ Q I
  · ext; simp
  rw [comap_equiv_eq_map_symm, map_symm_eq_iff, map_range_rTensor_subtype_lid]

variable {M' N' P' : Type*}
    [AddCommGroup M'] [AddCommGroup N'] [AddCommGroup P']
    [Module R M'] [Module R N'] [Module R P']
    {f' : M' →ₗ[R] N'} {g' : N' →ₗ[R] P'}
    (hfg' : Exact f' g') (hg' : Function.Surjective g')

include hg hg' hfg hfg' in
/-- Kernel of a product map (right-exactness of tensor product) -/
/-
**TensorProduct.map_ker** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TensorProduct.map_ker : ker (TensorProduct.map g g') = range (lTensor N f'
) ⊔ range (rTensor N' f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.lTensor_comp_rTensor`：lTensor_comp_rTensor (f : M ->ₗ[R] P) (g
 : N ->ₗ[R] Q) : (g.lTensor P).comp (f.rTensor N) = map f g
· 使用定理 `LinearMap.ker_comp`：ker_comp (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) 
: ker (g.comp f : M ->ₛₗ[τ₁₃] M₃) = comap f (ker g)
· 使用定理 `Function.Exact.linearMap_ker_eq`：∀ {R : Type u_1} {M : Type u_2} {N : Ty
pe u_4} {P : Type u_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 
: AddCommMonoid N] [i…
· 使用定理 `rTensor_exact`：rTensor_exact : Exact (rTensor Q f) (rTensor Q g)
· 使用定理 `Submodule.comap_map_eq`：comap_map_eq (f : M ->ₛₗ[τ₁₂] M₂) (p : Submodule
 R M) : comap f (map f p) = p ⊔ LinearMap.ker f
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `LinearMap.range_eq_map`：range_eq_map [RingHomSurjective τ₁₂] (f : M ->ₛₗ
[τ₁₂] M₂) : range f = map f ⊤
· 使用定理 `Submodule.map_comp`：map_comp [RingHomSurjective σ₂₃] [RingHomSurjective 
σ₁₃] (f : M ->ₛₗ[σ₁₂] M₂) (g : M₂ ->ₛₗ[σ₂₃] M₃) (p : Submodule R M) : map (g.com
p f : M …
· 使用定理 `LinearMap.rTensor_comp_lTensor`：rTensor_comp_lTensor (f : M ->ₗ[R] P) (g
 : N ->ₗ[R] Q) : (f.rTensor Q).comp (g.lTensor M) = map f g
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `LinearMap.rTensor_surjective`：LinearMap.rTensor_surjective (hg : Functio
n.Surjective g) : Function.Surjective (rTensor Q g)
· 使用定理 `lTensor_exact`：lTensor_exact : Exact (lTensor Q f) (lTensor Q g)

--- 原说明 ---
Kernel of a product map (right-exactness of tensor product)
-/
theorem TensorProduct.map_ker :
    ker (TensorProduct.map g g') = range (lTensor N f') ⊔ range (rTensor N' f) := by
  rw [← lTensor_comp_rTensor]
  rw [ker_comp]
  rw [← Exact.linearMap_ker_eq (rTensor_exact N' hfg hg)]
  rw [← Submodule.comap_map_eq]
  apply congr_arg₂ _ rfl
  rw [range_eq_map, ← Submodule.map_comp, rTensor_comp_lTensor,
    Submodule.map_top]
  rw [← lTensor_comp_rTensor, range_eq_map, Submodule.map_comp,
    Submodule.map_top]
  rw [range_eq_top.mpr (rTensor_surjective M' hg), Submodule.map_top]
  rw [Exact.linearMap_ker_eq (lTensor_exact P hfg' hg')]

end Modules

section Algebras

open Algebra.TensorProduct

open scoped TensorProduct

variable
    {R : Type*} [CommSemiring R]
    {A B : Type*} [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

/-- The ideal of `A ⊗[R] B` generated by `I` is the image of `I ⊗[R] B` -/
/-
**Ideal.map_includeLeft_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.map_includeLeft_eq (I : Ideal A) : (I.map (Algebra.TensorProduct.inc
ludeLeft : A ->ₐ[R] A otimes[R] B)).restrictScalars R = LinearMap.range (LinearM
ap.rTensor B (Submodule.subtype (I.restrictScalars R)))
参数：I : Ideal A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.coe_set_eq`：coe_set_eq : (p : Set B) = q ↔ p = q
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
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
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `Ideal.submodule_span_eq`：submodule_span_eq {s : Set α} : Submodule.span 
α s = Ideal.span s
· 使用定理 `Ideal.map.eq_1`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : Semir
ing R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   (I : Ideal R), I
deal…
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
The ideal of `A ⊗[R] B` generated by `I` is the image of `I ⊗[R] B`
-/
lemma Ideal.map_includeLeft_eq (I : Ideal A) :
    (I.map (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B)).restrictScalars R
      = LinearMap.range (LinearMap.rTensor B (Submodule.subtype (I.restrictScalars R))) := by
  rw [← SetLike.coe_set_eq]
  apply le_antisymm
  · intro x hx
    simp only [SetLike.mem_coe, LinearMap.mem_range]
    rw [Ideal.map, ← submodule_span_eq] at hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · intro x
      simp only [includeLeft_apply, Set.mem_image, SetLike.mem_coe]
      rintro ⟨y, hy, rfl⟩
      use ⟨y, hy⟩ ⊗ₜ[R] 1
      rfl
    · use 0
      simp only [map_zero]
    · rintro x y - - ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
      use x + y
      simp only [map_add]
    · rintro a x - ⟨x, hx, rfl⟩
      induction a with
      | zero =>
        use 0
        simp only [map_zero, smul_eq_mul, zero_mul]
      | tmul a b =>
        induction x with
        | zero =>
          use 0
          simp only [map_zero, smul_eq_mul, mul_zero]
        | tmul x y =>
          use (a • x) ⊗ₜ[R] (b * y)
          simp only [smul_eq_mul]
          with_unfolding_all rfl
        | add x y hx hy =>
          obtain ⟨x', hx'⟩ := hx
          obtain ⟨y', hy'⟩ := hy
          use x' + y'
          simp only [map_add, hx', smul_add, hy']
      | add a b ha hb =>
        obtain ⟨x', ha'⟩ := ha
        obtain ⟨y', hb'⟩ := hb
        use x' + y'
        simp only [map_add, ha', add_smul, hb']
  · rintro x ⟨y, rfl⟩
    induction y with
    | zero =>
        rw [map_zero]
        apply zero_mem
    | tmul a b =>
        simp only [LinearMap.rTensor_tmul, Submodule.coe_subtype]
        suffices (a : A) ⊗ₜ[R] b = ((1 : A) ⊗ₜ[R] b) * ((a : A) ⊗ₜ[R] (1 : B)) by
          simp only [Submodule.coe_restrictScalars, SetLike.mem_coe]
          rw [this]
          apply Ideal.mul_mem_left
          -- Note: adding `includeLeft` as a hint fixes a timeout https://github.com/leanprover-community/mathlib4/pull/8386
          apply Ideal.mem_map_of_mem includeLeft
          exact Submodule.coe_mem a
        simp only [Algebra.TensorProduct.tmul_mul_tmul,
          mul_one, one_mul]
    | add x y hx hy =>
        rw [map_add]
        apply Submodule.add_mem _ hx hy

/-- The ideal of `A ⊗[R] B` generated by `I` is the image of `A ⊗[R] I` -/
/-
**Ideal.map_includeRight_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.map_includeRight_eq (I : Ideal B) : (I.map (Algebra.TensorProduct.in
cludeRight : B ->ₐ[R] A otimes[R] B)).restrictScalars R = LinearMap.range (Linea
rMap.lTensor A (Submodule.subtype (I.restrictScalars R)))
参数：I : Ideal B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.coe_set_eq`：coe_set_eq : (p : Set B) = q ↔ p = q
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
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
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `Ideal.submodule_span_eq`：submodule_span_eq {s : Set α} : Submodule.span 
α s = Ideal.span s
· 使用定理 `Ideal.map.eq_1`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : Semir
ing R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   (I : Ideal R), I
deal…
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
The ideal of `A ⊗[R] B` generated by `I` is the image of `A ⊗[R] I`
-/
lemma Ideal.map_includeRight_eq (I : Ideal B) :
    (I.map (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B)).restrictScalars R
      = LinearMap.range (LinearMap.lTensor A (Submodule.subtype (I.restrictScalars R))) := by
  rw [← SetLike.coe_set_eq]
  apply le_antisymm
  · intro x hx
    simp only [SetLike.mem_coe, LinearMap.mem_range]
    rw [Ideal.map, ← submodule_span_eq] at hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · intro x
      simp only [includeRight_apply, Set.mem_image, SetLike.mem_coe]
      rintro ⟨y, hy, rfl⟩
      use 1 ⊗ₜ[R] ⟨y, hy⟩
      rfl
    · use 0
      simp only [map_zero]
    · rintro x y - - ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
      use x + y
      simp only [map_add]
    · rintro a x - ⟨x, hx, rfl⟩
      induction a with
      | zero =>
        use 0
        simp only [map_zero, smul_eq_mul, zero_mul]
      | tmul a b =>
        induction x with
        | zero =>
          use 0
          simp only [map_zero, smul_eq_mul, mul_zero]
        | tmul x y =>
          use (a * x) ⊗ₜ[R] (b • y)
          simp only [LinearMap.lTensor_tmul, Submodule.coe_subtype, smul_eq_mul, tmul_mul_tmul]
          rfl
        | add x y hx hy =>
          obtain ⟨x', hx'⟩ := hx
          obtain ⟨y', hy'⟩ := hy
          use x' + y'
          simp only [map_add, hx', smul_add, hy']
      | add a b ha hb =>
        obtain ⟨x', ha'⟩ := ha
        obtain ⟨y', hb'⟩ := hb
        use x' + y'
        simp only [map_add, ha', add_smul, hb']
  · rintro x ⟨y, rfl⟩
    induction y with
    | zero =>
        rw [map_zero]
        apply zero_mem
    | tmul a b =>
        simp only [LinearMap.lTensor_tmul, Submodule.coe_subtype]
        suffices a ⊗ₜ[R] (b : B) = (a ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] (b : B)) by
          rw [this]
          simp only [Submodule.coe_restrictScalars, SetLike.mem_coe]
          apply Ideal.mul_mem_left
          -- Note: adding `includeRight` as a hint fixes a timeout https://github.com/leanprover-community/mathlib4/pull/8386
          apply Ideal.mem_map_of_mem includeRight
          exact Submodule.coe_mem b
        simp only [Algebra.TensorProduct.tmul_mul_tmul,
          mul_one, one_mul]
    | add x y hx hy =>
        rw [map_add]
        apply Submodule.add_mem _ hx hy

variable (A) in
/-
**TensorProduct.AlgebraTensorModule.range_lTensor_idealMap** 是 Mathlib 中的一个引理，位于
命名空间 ``。
形式化陈述：TensorProduct.AlgebraTensorModule.range_lTensor_idealMap (S : Type*) [Comm
Semiring S] [Algebra R S] [Algebra S A] [IsScalarTower R S A] (I : Ideal B) : Li
nearMap.range (lTensor S A (I.subtype.restrictScalars R)) = (I.map (includeRight
 (A
参数：S : Type*；I : Ideal B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Submodule.restrictScalars_injective`：restrictScalars_injective : Functio
n.Injective (restrictScalars S : Submodule R M -> Submodule S M)
· 使用引理 `Ideal.map_includeRight_eq`：Ideal.map_includeRight_eq (I : Ideal B) : (I.
map (Algebra.TensorProduct.includeRight : B ->ₐ[R] A otimes[R] B)).restrictScala
rs R = LinearMa…
-/
lemma TensorProduct.AlgebraTensorModule.range_lTensor_idealMap (S : Type*) [CommSemiring S]
    [Algebra R S] [Algebra S A] [IsScalarTower R S A] (I : Ideal B) :
    LinearMap.range (lTensor S A (I.subtype.restrictScalars R)) =
      (I.map (includeRight (A := A) (R := R))).restrictScalars S := by
  rw [← (Submodule.restrictScalars_injective R _ _).eq_iff]
  exact (I.map_includeRight_eq (R := R) (A := A)).symm

-- Now, we can prove the right exactness properties of the tensor product,
-- in its versions for algebras

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  {A B C D : Type*} [Ring A] [Ring B] [Ring C] [Ring D]
  [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D] [Algebra S A] [Algebra S B]
  [IsScalarTower R S A] [IsScalarTower R S B]
  (f : A →ₐ[S] B) (g : C →ₐ[R] D)

/-- If `g` is surjective, then the kernel of `(id A) ⊗ g` is generated by the kernel of `g` -/
/-
**Algebra.TensorProduct.lTensor_ker** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.TensorProduct.lTensor_ker (hg : Function.Surjective g) : RingHom.k
er (map (AlgHom.id R A) g) = (RingHom.ker g).map (Algebra.TensorProduct.includeR
ight : C ->ₐ[R] A otimes[R] C)
参数：hg : Function.Surjective g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.restrictScalars_inj`：restrictScalars_inj {V₁ V₂ : Submodule R 
M} : restrictScalars S V₁ = restrictScalars S V₂ ↔ V₁ = V₂
· 使用引理 `Ideal.map_includeRight_eq`：Ideal.map_includeRight_eq (I : Ideal B) : (I.
map (Algebra.TensorProduct.includeRight : B ->ₐ[R] A otimes[R] B)).restrictScala
rs R = LinearMa…
· 使用定理 `Function.Exact.linearMap_ker_eq`：∀ {R : Type u_1} {M : Type u_2} {N : Ty
pe u_4} {P : Type u_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 
: AddCommMonoid N] [i…
· 使用定理 `lTensor_exact`：lTensor_exact : Exact (lTensor Q f) (lTensor Q g)
· 使用引理 `LinearMap.exact_subtype_ker_map`：exact_subtype_ker_map (g : N ->ₗ[R] P) 
: Exact (Submodule.subtype (ker g)) g

--- 原说明 ---
If `g` is surjective, then the kernel of `(id A) ⊗ g` is generated by the kernel
 of `g`
-/
lemma Algebra.TensorProduct.lTensor_ker (hg : Function.Surjective g) :
    RingHom.ker (map (AlgHom.id R A) g) =
      (RingHom.ker g).map (Algebra.TensorProduct.includeRight : C →ₐ[R] A ⊗[R] C) := by
  rw [← Submodule.restrictScalars_inj R]
  have : (RingHom.ker (map (AlgHom.id R A) g)).restrictScalars R =
    LinearMap.ker (LinearMap.lTensor A (AlgHom.toLinearMap g)) := rfl
  rw [this, Ideal.map_includeRight_eq]
  rw [(lTensor_exact A g.toLinearMap.exact_subtype_ker_map hg).linearMap_ker_eq]
  rfl

/-- If `f` is surjective, then the kernel of `f ⊗ (id B)` is generated by the kernel of `f` -/
/-
**Algebra.TensorProduct.rTensor_ker** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.TensorProduct.rTensor_ker (hf : Function.Surjective f) : RingHom.k
er (map f (AlgHom.id R C)) = (RingHom.ker f).map (Algebra.TensorProduct.includeL
eft : A ->ₐ[R] A otimes[R] C)
参数：hf : Function.Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.restrictScalars_inj`：restrictScalars_inj {V₁ V₂ : Submodule R 
M} : restrictScalars S V₁ = restrictScalars S V₂ ↔ V₁ = V₂
· 使用引理 `Ideal.map_includeLeft_eq`：Ideal.map_includeLeft_eq (I : Ideal A) : (I.ma
p (Algebra.TensorProduct.includeLeft : A ->ₐ[R] A otimes[R] B)).restrictScalars 
R = LinearMap.…
· 使用定理 `Function.Exact.linearMap_ker_eq`：∀ {R : Type u_1} {M : Type u_2} {N : Ty
pe u_4} {P : Type u_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 
: AddCommMonoid N] [i…
· 使用定理 `rTensor_exact`：rTensor_exact : Exact (rTensor Q f) (rTensor Q g)
· 使用引理 `LinearMap.exact_subtype_ker_map`：exact_subtype_ker_map (g : N ->ₗ[R] P) 
: Exact (Submodule.subtype (ker g)) g

--- 原说明 ---
If `f` is surjective, then the kernel of `f ⊗ (id B)` is generated by the kernel
 of `f`
-/
lemma Algebra.TensorProduct.rTensor_ker (hf : Function.Surjective f) :
    RingHom.ker (map f (AlgHom.id R C)) =
      (RingHom.ker f).map (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] C) := by
  rw [← Submodule.restrictScalars_inj R]
  have : (RingHom.ker (map f (AlgHom.id R C))).restrictScalars R =
    LinearMap.ker (LinearMap.rTensor C (f.restrictScalars R).toLinearMap) := rfl
  rw [this, Ideal.map_includeLeft_eq]
  rw [(rTensor_exact C (f.restrictScalars R).toLinearMap.exact_subtype_ker_map hf).linearMap_ker_eq]
  rfl
/-
**Algebra.TensorProduct.map_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.TensorProduct.map_surjective (hf : Function.Surjective f) (hg : Fu
nction.Surjective g) : Function.Surjective (map f g)
参数：hf : Function.Surjective f；hg : Function.Surjective g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.map_surjective`：TensorProduct.map_surjective : Function.Su
rjective (TensorProduct.map g g')
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
-/
theorem Algebra.TensorProduct.map_surjective
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    Function.Surjective (map f g) :=
  _root_.TensorProduct.map_surjective (g := f.toLinearMap.restrictScalars R) hf hg

/-- If `f` and `g` are surjective morphisms of algebras, then
  the kernel of `Algebra.TensorProduct.map f g` is generated by the kernels of `f` and `g` -/
/-
**Algebra.TensorProduct.map_ker** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.TensorProduct.map_ker (hf : Function.Surjective f) (hg : Function.
Surjective g) : RingHom.ker (map f g) = (RingHom.ker f).map (Algebra.TensorProdu
ct.includeLeft : A ->ₐ[R] A otimes[R] C) ⊔ (RingHom.ker g).map (Algebra.TensorPr
oduct.includeRight : C ->ₐ[R] A otimes[R] C)
参数：hf : Function.Surjective f；hg : Function.Surjective g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Algebra.TensorProduct.ext`：ext ⦃f g : (A otimes[R] B) ->ₐ[S] C⦄ (ha : f.
comp includeLeft = g.comp includeLeft) (hb : (f.restrictScalars R).comp includeR
ight = (g.restr…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.comap_ker`：comap_ker (f : S ->+* R) (g : T ->+* S) : (ker f).com
ap g = ker (f.comp g)
· 使用引理 `Algebra.TensorProduct.lTensor_ker`：Algebra.TensorProduct.lTensor_ker (hg
 : Function.Surjective g) : RingHom.ker (map (AlgHom.id R A) g) = (RingHom.ker g
).map (Algebra.TensorPr…
· 使用定理 `RingHom.ker_eq_comap_bot`：ker_eq_comap_bot (f : F) : ker f = Ideal.comap
 f ⊥
· 使用定理 `Ideal.comap_map_of_surjective`：comap_map_of_surjective (hf : Function.Su
rjective f) (I : Ideal R) : comap f (map f I) = I ⊔ comap f ⊥
· 使用定理 `LinearMap.lTensor_surjective`：LinearMap.lTensor_surjective (hg : Functio
n.Surjective g) : Function.Surjective (lTensor Q g)
· 使用引理 `Algebra.TensorProduct.rTensor_ker`：Algebra.TensorProduct.rTensor_ker (hf
 : Function.Surjective f) : RingHom.ker (map f (AlgHom.id R C)) = (RingHom.ker f
).map (Algebra.TensorPr…
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Ideal.map_map`：map_map {T : Type*} [Semiring T] {I : Ideal R} (f : R ->+
* S) (g : S ->+* T) : (I.map f).map g = I.map (g.comp f)
· 使用定理 `AlgHom.comp_toRingHom`：comp_toRingHom (φ₁ : B ->ₐ[R] C) (φ₂ : A ->ₐ[R] B
) : (φ₁.comp φ₂ : A ->+* C) = (φ₁ : B ->+* C).comp ↑φ₂
· 使用定理 `Algebra.TensorProduct.map_comp_includeLeft`：map_comp_includeLeft (f : A 
->ₐ[S] C) (g : B ->ₐ[R] D) : (map f g).comp includeLeft = includeLeft.comp f

--- 原说明 ---
If `f` and `g` are surjective morphisms of algebras, then
  the kernel of `Algebra.TensorProduct.map f g` is generated by the kernels of `
f` and `g`
-/
theorem Algebra.TensorProduct.map_ker (hf : Function.Surjective f) (hg : Function.Surjective g) :
    RingHom.ker (map f g) =
      (RingHom.ker f).map (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] C) ⊔
        (RingHom.ker g).map (Algebra.TensorProduct.includeRight : C →ₐ[R] A ⊗[R] C) := by
  -- rewrite map f g as the composition of two maps
  have : map f g = (map f (AlgHom.id R D)).comp (map (AlgHom.id S A) g) := ext rfl rfl
  rw [this]
  -- this needs some rewriting to RingHom
  -- TODO: can `RingHom.comap_ker` take an arbitrary `RingHomClass`, rather than just `RingHom`?
  simp only [AlgHom.ker_coe, AlgHom.comp_toRingHom]
  rw [← RingHom.comap_ker]
  simp only [← AlgHom.ker_coe]
  -- apply one step of exactness
  rw [← Algebra.TensorProduct.lTensor_ker _ hg, RingHom.ker_eq_comap_bot (map (AlgHom.id R A) g)]
  rw [← Ideal.comap_map_of_surjective (map (AlgHom.id R A) g) (LinearMap.lTensor_surjective A hg)]
  -- apply the other step of exactness
  rw [Algebra.TensorProduct.rTensor_ker _ hf]
  apply congr_arg₂ _ rfl
  simp only [AlgHom.coe_ideal_map, Ideal.map_map]
  rw [← AlgHom.comp_toRingHom, Algebra.TensorProduct.map_comp_includeLeft]
  rfl

end Algebras

