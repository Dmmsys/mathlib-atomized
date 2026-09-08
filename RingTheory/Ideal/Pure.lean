/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Flat.Tensor
public import Mathlib.RingTheory.Ideal.IdempotentFG
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import Mathlib.RingTheory.LocalProperties.Basic

/-!
# Pure ideals

An ideal `I` of a ring `R` is called pure if `R ⧸ I` is flat over `R`
(see [Stacks 04PR](https://stacks.math.columbia.edu/tag/04PR)). In this file we show
some properties of such ideals.

## Main results and definitions

- `Ideal.Pure`: An ideal `I` of `R` is pure if `R ⧸ I` is `R`-flat.
- `Ideal.inf_eq_mul_of_pure`: If `I` is pure, `I ⊓ J = I * J` for every ideal `J`.
- `Ideal.Pure.of_inf_eq_mul`: If for any f.g. ideal `J`, the equality `I ⊓ J = I * J` holds, then
  `I` is pure.
- `Ideal.zeroLocus_inj_of_pure`: If `I` and `J` are pure ideals such that `V(I) = V(J)`, then
  `I = J`.
-/

public section

variable {R : Type*} [CommRing R]

open TensorProduct PrimeSpectrum

/-- An ideal `I` of `R` is pure if `R ⧸ I` is a flat `R`-module. -/
@[stacks 04PR]
/-
**Ideal.Pure** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Ideal.Pure (I : Ideal R) : Prop
参数：I : Ideal R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An ideal `I` of `R` is pure if `R ⧸ I` is a flat `R`-module.
-/
abbrev Ideal.Pure (I : Ideal R) : Prop :=
  Module.Flat R (R ⧸ I)
/-
**injective_lTensor_quotient_iff_inf_eq_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：injective_lTensor_quotient_iff_inf_eq_mul (I J : Ideal R) : Function.Injec
tive (J.subtype.lTensor (R ⧸ I)) ↔ I ⊓ J = I * J
参数：I J : Ideal R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.map_smul''`：map_smul'' (f : M ->ₗ[R] M') : (I • N).map f = I •
 N.map f
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `Ideal.Quotient.isScalarTower`：∀ (R₁ : Type u_1) (R₂ : Type u_2) {A : Typ
e u_3} [inst : CommSemiring R₁] [inst_1 : CommSemiring R₂] [inst_2 : Ring A]   [
inst_3 : Algebra R…
· 使用定理 `Submodule.linearMap_qext`：linearMap_qext ⦃f g : M ⧸ p ->ₛₗ[τ₁₂] M₂⦄ (h :
 f.comp p.mkQ = g.comp p.mkQ) : f = g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用引理 `TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul`：quotTensorEquivQuotSM
ul_mk_one_tmul (I : Ideal R) (x : M) : quotTensorEquivQuotSMul M I (1 otimesₜ x)
 = Submodule.Quotient.mk x
· 使用引理 `Algebra.TensorProduct.tmul_one_eq_one_tmul`：tmul_one_eq_one_tmul (r : R)
 : algebraMap R A r otimesₜ[R] 1 = 1 otimesₜ algebraMap R B r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用引理 `Submodule.ker_mapQ`：ker_mapQ (f : M ->ₛₗ[τ₁₂] M₂) (h) : ker (p.mapQ q f 
h) = (comap f q).map p.mkQ
· 使用定理 `Submodule.ker_mkQ`：ker_mkQ : ker p.mkQ = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.map_le_map_iff_of_injective`：map_le_map_iff_of_injective (p q 
: Submodule R M) : p.map f <= q.map f ↔ p <= q
· 使用定理 `Submodule.injective_subtype`：injective_subtype : Injective p.subtype
（共 36 条，此处仅展示前 30 条）
-/
lemma injective_lTensor_quotient_iff_inf_eq_mul (I J : Ideal R) :
    Function.Injective (J.subtype.lTensor (R ⧸ I)) ↔ I ⊓ J = I * J := by
  let f : J ⧸ (I • ⊤ : Submodule R J) →ₗ[R] R ⧸ I :=
    Submodule.mapQ _ _ J.subtype <| by
      simp [← Submodule.map_le_iff_le_comap, Ideal.mul_le_left]
  have : J.subtype.lTensor (R ⧸ I) =
      (TensorProduct.rid R (R ⧸ I)).symm ∘ₗ f ∘ₗ TensorProduct.quotTensorEquivQuotSMul J I := by
    ext
    simp [f, ← Ideal.Quotient.algebraMap_eq, Algebra.TensorProduct.tmul_one_eq_one_tmul]
  rw [this]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, EmbeddingLike.comp_injective,
    EquivLike.injective_comp, ← LinearMap.ker_eq_bot, f, Submodule.ker_mapQ,
    ← LinearMap.le_ker_iff_map, Submodule.ker_mkQ,
    ← (Submodule.map_le_map_iff_of_injective J.injective_subtype)]
  simp [inf_comm, le_antisymm_iff, Ideal.mul_le_inf (I := I) (J := J)]

@[stacks 04PS "(1) => (2)"]
/-
**Ideal.inf_eq_mul_of_pure** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.inf_eq_mul_of_pure (I J : Ideal R) [I.Pure] : I ⊓ J = I * J
参数：I J : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `injective_lTensor_quotient_iff_inf_eq_mul`：injective_lTensor_quotient_if
f_inf_eq_mul (I J : Ideal R) : Function.Injective (J.subtype.lTensor (R ⧸ I)) ↔ 
I ⊓ J = I * J
· 使用定理 `Module.Flat.lTensor_preserves_injective_linearMap`：lTensor_preserves_inj
ective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Function.Injective f) : Funct
ion.Injective (f.lTensor M)
· 使用定理 `Submodule.injective_subtype`：injective_subtype : Injective p.subtype
-/
lemma Ideal.inf_eq_mul_of_pure (I J : Ideal R) [I.Pure] :
    I ⊓ J = I * J := by
  rw [← injective_lTensor_quotient_iff_inf_eq_mul]
  apply Module.Flat.lTensor_preserves_injective_linearMap
  exact J.injective_subtype

/-- If `I` is pure, `I ^ 2 = I`. The converse holds if `I` is finitely generated, see
`Ideal.Pure.of_isIdempotentElem`. -/
/-
**Ideal.isIdempotentElem_of_pure** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.isIdempotentElem_of_pure (I : Ideal R) [I.Pure] : IsIdempotentElem I
参数：I : Ideal R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `I` is pure, `I ^ 2 = I`. The converse holds if `I` is finitely generated, se
e
`Ideal.Pure.of_isIdempotentElem`.
-/
lemma Ideal.isIdempotentElem_of_pure (I : Ideal R) [I.Pure] : IsIdempotentElem I := by
  simp [IsIdempotentElem, ← Ideal.inf_eq_mul_of_pure]
/-
**Ideal.Pure.of_isIdempotentElem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.Pure.of_isIdempotentElem {I : Ideal R} (h : I.FG) (h' : IsIdempotent
Elem I) : I.Pure
参数：h : I.FG；h' : IsIdempotentElem I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.isIdempotentElem_iff_of_fg`：isIdempotentElem_iff_of_fg {R : Type*}
 [CommRing R] (I : Ideal R) (h : I.FG) : IsIdempotentElem I ↔ exists e : R, IsId
empotentElem e ∧ I = R…
· 使用引理 `Module.Flat.of_linearEquiv`：of_linearEquiv [Flat R M] (e : N ≃ₗ[R] M) : 
Flat R N
· 使用引理 `IsIdempotentElem.one_sub`：one_sub (h : IsIdempotentElem a) : IsIdempoten
tElem (1 - a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Module.Flat.of_retract`：of_retract [f : Flat R M] (i : N ->ₗ[R] M) (r : 
M ->ₗ[R] N) (h : r.comp i = LinearMap.id) : Flat R N
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma Ideal.Pure.of_isIdempotentElem {I : Ideal R} (h : I.FG) (h' : IsIdempotentElem I) :
    I.Pure := by
  rw [Ideal.isIdempotentElem_iff_of_fg _ h] at h'
  obtain ⟨e, he, rfl⟩ := h'
  have : Module.Flat R ((R ⧸ R ∙ e) × R ⧸ span {1 - e}) :=
    .of_linearEquiv <| AlgEquiv.prodQuotientOfIsIdempotentElem R he he.one_sub (by simp)
      (by grind [IsIdempotentElem]) |>.toLinearEquiv.symm
  apply Module.Flat.of_retract (LinearMap.inl R _ (R ⧸ span {1 - e})) (LinearMap.fst R _ _)
  simp

@[stacks 04PS "(3) => (1)"]
/-
**Ideal.Pure.of_inf_eq_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.Pure.of_inf_eq_mul (I : Ideal R) (H : forall ⦃J : Ideal R⦄, J.FG -> 
I ⊓ J = I * J) : I.Pure
参数：I : Ideal R；H : forall ⦃J : Ideal R⦄, J.FG -> I ⊓ J = I * J。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.Pure.eq_1`：∀ {R : Type u_1} [inst : CommRing R] (I : Ideal R), I.P
ure = Module.Flat R (R ⧸ I)
· 使用定理 `Module.Flat.iff_lTensor_injective`：iff_lTensor_injective : Flat R M ↔ fo
rall ⦃I : Ideal R⦄, I.FG -> Function.Injective (I.subtype.lTensor M)
· 使用引理 `injective_lTensor_quotient_iff_inf_eq_mul`：injective_lTensor_quotient_if
f_inf_eq_mul (I J : Ideal R) : Function.Injective (J.subtype.lTensor (R ⧸ I)) ↔ 
I ⊓ J = I * J
-/
lemma Ideal.Pure.of_inf_eq_mul (I : Ideal R) (H : ∀ ⦃J : Ideal R⦄, J.FG → I ⊓ J = I * J) :
    I.Pure := by
  rw [Pure, Module.Flat.iff_lTensor_injective]
  intro J hJ
  rw [injective_lTensor_quotient_iff_inf_eq_mul]
  exact H hJ

@[stacks 04PS "(1) => (5)"]
/-
**Ideal.exists_eq_mul_of_pure** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.exists_eq_mul_of_pure {I : Ideal R} [I.Pure] {x : R} (hx : x in I) :
 exists y in I, x = x * y
参数：hx : x in I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Ideal.inf_eq_mul_of_pure`：Ideal.inf_eq_mul_of_pure (I J : Ideal R) [I.Pu
re] : I ⊓ J = I * J
· 使用定理 `Ideal.subset_span`：subset_span {s : Set α} : s subseteq span s
· 使用定理 `Ideal.mem_mul_span_singleton`：mem_mul_span_singleton {x y : R} {I : Idea
l R} [I.IsTwoSided] : x in I * span {y} ↔ exists z in I, z * y = x
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
lemma Ideal.exists_eq_mul_of_pure {I : Ideal R} [I.Pure] {x : R} (hx : x ∈ I) :
    ∃ y ∈ I, x = x * y := by
  suffices h : x ∈ I * Ideal.span {x} by
    rw [Ideal.mem_mul_span_singleton] at h
    grind
  rw [← I.inf_eq_mul_of_pure]
  exact ⟨hx, subset_span rfl⟩

@[stacks 04PS "(5) => (7)"]
/-
**Ideal.le_ker_atPrime_of_forall_exists_eq_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.le_ker_atPrime_of_forall_exists_eq_mul {I : Ideal R} (h : forall x i
n I, exists y in I, x = x * y) {p : Ideal R} [p.IsPrime] (hle : I <= p) : I <= R
ingHom.ker (algebraMap R <| Localization.AtPrime p)
参数：h : forall x in I, exists y in I, x = x * y；hle : I <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.algebraMap_isUnit_iff`：algebraMap_isUnit_iff {x : R} : Is
Unit (algebraMap R S x) ↔ exists m in M, x ∣ m
· 使用定理 `Ideal.one_notMem`：one_notMem (I : Ideal α) [hI : I.IsPrime] : 1 ∉ I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `Ideal.add_mem`：∀ {α : Type u} [inst : Semiring α] (I : Ideal α) {a b : α
}, a ∈ I → b ∈ I → a + b ∈ I
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsUnit.mul_left_eq_zero`：mul_left_eq_zero {a b : M₀} (hb : IsUnit b) : a
 * b = 0 ↔ a = 0
· 使用定理 `RingHom.map_zero`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring 
α} {x_1 : NonAssocSemiring β} (f : α →+* β), f 0 = 0
-/
lemma Ideal.le_ker_atPrime_of_forall_exists_eq_mul {I : Ideal R}
    (h : ∀ x ∈ I, ∃ y ∈ I, x = x * y) {p : Ideal R} [p.IsPrime] (hle : I ≤ p) :
    I ≤ RingHom.ker (algebraMap R <| Localization.AtPrime p) := by
  intro x hx
  obtain ⟨y, hy, heq⟩ := h _ hx
  have : IsUnit (algebraMap R (Localization.AtPrime p) (1 - y)) := by
    rw [IsLocalization.algebraMap_isUnit_iff p.primeCompl]
    refine ⟨1 - y, fun hz ↦ p.one_notMem ?_, by simp⟩
    rw [← sub_add_cancel 1 y]
    exact Ideal.add_mem _ hz (hle hy)
  have hzero : x * (1 - y) = 0 := by simp [mul_sub, ← heq]
  simp only [RingHom.mem_ker, ← this.mul_left_eq_zero, ← RingHom.map_mul, hzero, RingHom.map_zero]
/-
**Ideal.ker_piRingHom_atPrime_eq_of_pure** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.ker_piRingHom_atPrime_eq_of_pure (I : Ideal R) [I.Pure] : RingHom.ke
r (RingHom.pi fun p : zeroLocus (I : Set R) => algebraMap R (Localization.AtPrim
e p.val.asIdeal)) = I
参数：I : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.ker_ringHom`：∀ {S : Type v} [inst : Semiring S] {ι : Type u_3} {R : ι
 → Type u_4} [inst_1 : (i : ι) → Semiring (R i)]   (φ : (i : ι) → S →+* R i), Ri
ngHo…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iInf_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {f : ι → α} {a : α} (i : ι), f i ≤ a → iInf f ≤ a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `Ideal.iInf_ker_le`：Ideal.iInf_ker_le (I : Ideal R) : ⨅ (p : Ideal R) (_ 
: p.IsPrime) (_ : I <= p), RingHom.ker (algebraMap R (Localization.AtPrime p)) <
= I
· 使用定理 `RingHom.mem_ker`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : Semi
ring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHomClass F R
 S] {…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `RingHom.pi_apply`：∀ {I : Type u} {f : I → Type u_1} {γ : Type u_2} [inst
 : (i : I) → NonAssocSemiring (f i)] [inst_1 : NonAssocSemiring γ]   (g : (i : I
) → γ …
· 使用定理 `Pi.zero_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zer
o (M i)] (i : ι), 0 i = 0
· 使用引理 `Ideal.le_ker_atPrime_of_forall_exists_eq_mul`：Ideal.le_ker_atPrime_of_fo
rall_exists_eq_mul {I : Ideal R} (h : forall x in I, exists y in I, x = x * y) {
p : Ideal R} [p.IsPrime] (hle : I …
· 使用引理 `Ideal.exists_eq_mul_of_pure`：Ideal.exists_eq_mul_of_pure {I : Ideal R} [
I.Pure] {x : R} (hx : x in I) : exists y in I, x = x * y
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma Ideal.ker_piRingHom_atPrime_eq_of_pure (I : Ideal R) [I.Pure] :
    RingHom.ker
      (RingHom.pi fun p : zeroLocus (I : Set R) ↦
        algebraMap R (Localization.AtPrime p.val.asIdeal)) = I := by
  refine le_antisymm ?_ fun x hx ↦ ?_
  · rw [Pi.ker_ringHom]
    refine le_trans ?_ I.iInf_ker_le
    simp only [le_iInf_iff]
    exact fun i hi hle ↦ iInf_le_of_le ⟨⟨i, hi⟩, hle⟩ le_rfl
  · rw [RingHom.mem_ker]
    ext p
    rw [RingHom.pi_apply, Pi.zero_apply]
    exact Ideal.le_ker_atPrime_of_forall_exists_eq_mul
      (fun x hx ↦ Ideal.exists_eq_mul_of_pure hx) p.2 hx

@[stacks 04PT]
/-
**Ideal.zeroLocus_inj_of_pure** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.zeroLocus_inj_of_pure {I J : Ideal R} [I.Pure] [J.Pure] : zeroLocus 
(I : Set R) = zeroLocus J ↔ I = J
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Ideal.ker_piRingHom_atPrime_eq_of_pure`：Ideal.ker_piRingHom_atPrime_eq_o
f_pure (I : Ideal R) [I.Pure] : RingHom.ker (RingHom.pi fun p : zeroLocus (I : S
et R) => algebraMap R (Local…
-/
lemma Ideal.zeroLocus_inj_of_pure {I J : Ideal R} [I.Pure] [J.Pure] :
    zeroLocus (I : Set R) = zeroLocus J ↔ I = J := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  rw [← I.ker_piRingHom_atPrime_eq_of_pure, ← J.ker_piRingHom_atPrime_eq_of_pure]
  generalize hs : zeroLocus (I : Set R) = s
  generalize ht : zeroLocus (J : Set R) = t
  obtain rfl : s = t := by rw [← hs, ← ht, h]
  rfl
