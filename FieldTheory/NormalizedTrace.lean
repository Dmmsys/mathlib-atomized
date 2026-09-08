/-
Copyright (c) 2025 Michal Staromiejski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Staromiejski
-/
module

public import Mathlib.RingTheory.Trace.Basic

/-!

# Normalized trace

This file defines the *normalized trace* map; that is, an `F`-linear map from the algebraic closure
of `F` to `F` defined as the trace of an element from its adjoin extension divided by its degree.

To avoid heavy imports, we define it here as a map from an arbitrary algebraic (equivalently
integral) extension of `F`.

## Main definitions

- `normalizedTrace`: the trace of an element from the simple adjoin divided by the degree;
  it is a non-trivial `F`-linear map from an arbitrary algebraic extension `K` to `F`.

## Main results

- `normalizedTrace_intermediateField`: for a tower `K / E / F` of algebraic extensions,
  `normalizedTrace F E` agrees with `normalizedTrace F K` on `E`.
- `normalizedTrace_trans`: for a tower `K / E / F` of algebraic extensions, the normalized trace
  from `K` to `E` composed with the normalized trace from `E` to `F` equals the normalized trace
  from `K` to `F`.
- `normalizedTrace_self`: `normalizedTrace F F` is the identity map.

-/

@[expose] public section

namespace Algebra

variable (F K : Type*) [Field F] [Field K] [Algebra F K]

open IntermediateField

set_option backward.privateInPublic true in
/- The normalized trace function from an extension `K` to the base field `F`.
Note: this definition does not require the extension `K / F` to be integral (algebraic)
nor the fields to be of characteristic zero. -/
/-
**Algebra.normalizedTraceAux** 是 Mathlib 中的一个定义，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The normalized trace function from an extension `K` to the base field `F`.
Note: this definition does not require the extension `K / F` to be integral (alg
ebraic)
nor the fields to be of characteristic zero.
-/
private noncomputable def normalizedTraceAux (a : K) : F :=
  (Module.finrank F F⟮a⟯ : F)⁻¹ • trace F F⟮a⟯ (AdjoinSimple.gen F a)
/-
**Algebra.normalizedTraceAux_def** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem normalizedTraceAux_def (a : K) : normalizedTraceAux F K a =
    (Module.finrank F F⟮a⟯ : F)⁻¹ • trace F F⟮a⟯ (AdjoinSimple.gen F a) := rfl
/-
**Algebra.normalizedTraceAux_map** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem normalizedTraceAux_map {E : Type*} [Field E] [Algebra F E] (f : E →ₐ[F] K) (a : E) :
    normalizedTraceAux F K (f a) = normalizedTraceAux F E a := by
  let e := (F⟮a⟯.equivMap f).trans (equivOfEq <| Set.image_singleton ▸ adjoin_map F {a} f)
  simp_rw [normalizedTraceAux, ← LinearEquiv.finrank_eq e.toLinearEquiv]
  congr
  exact trace_eq_of_algEquiv e <| AdjoinSimple.gen F a
/-
**Algebra.normalizedTraceAux_intermediateField** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
a`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem normalizedTraceAux_intermediateField {E : IntermediateField F K} (a : E) :
    normalizedTraceAux F K a = normalizedTraceAux F E a :=
  normalizedTraceAux_map F K E.val a

variable [CharZero F]

variable {K} in
/-
**Algebra.normalizedTraceAux_eq_of_finiteDimensional** 是 Mathlib 中的一个定理，位于命名空间 `
Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem normalizedTraceAux_eq_of_finiteDimensional [FiniteDimensional F K] (a : K) :
    normalizedTraceAux F K a = (Module.finrank F K : F)⁻¹ • trace F K a := by
  have h := (Nat.cast_ne_zero (R := F)).mpr <|
    Nat.pos_iff_ne_zero.mp <| Module.finrank_pos (R := F⟮a⟯) (M := K)
  rw [smul_eq_mul, mul_comm, ← div_eq_mul_inv, trace_eq_trace_adjoin F a,
    ← Module.finrank_mul_finrank F F⟮a⟯ K, nsmul_eq_mul, Nat.cast_mul, mul_comm,
    mul_div_mul_right _ _ h, div_eq_mul_inv, mul_comm, ← smul_eq_mul, normalizedTraceAux_def]

variable [Algebra.IsIntegral F K]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The normalized trace map from an algebraic extension `K` to the base field `F`. -/
/-
**Algebra.normalizedTrace** 是 Mathlib 中的一个定义，位于命名空间 `Algebra`。
形式化陈述：normalizedTrace : K ->ₗ[F] F where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The normalized trace map from an algebraic extension `K` to the base field `F`.
-/
noncomputable def normalizedTrace : K →ₗ[F] F where
  toFun := normalizedTraceAux F K
  map_add' a b := by
    let E := F⟮a⟯ ⊔ F⟮b⟯
    have : FiniteDimensional F F⟮a⟯ := adjoin.finiteDimensional (IsIntegral.isIntegral a)
    have : FiniteDimensional F F⟮b⟯ := adjoin.finiteDimensional (IsIntegral.isIntegral b)
    have ha : a ∈ E := (le_sup_left : F⟮a⟯ ≤ E) <| mem_adjoin_simple_self F a
    have hb : b ∈ E := (le_sup_right : F⟮b⟯ ≤ E) <| mem_adjoin_simple_self F b
    have hab : a + b ∈ E := IntermediateField.add_mem E ha hb
    let a' : E := ⟨a, ha⟩
    let b' : E := ⟨b, hb⟩
    let ab' : E := ⟨a + b, hab⟩
    rw [normalizedTraceAux_intermediateField F K a',
      normalizedTraceAux_intermediateField F K b',
      normalizedTraceAux_intermediateField F K ab',
      normalizedTraceAux_eq_of_finiteDimensional F a',
      normalizedTraceAux_eq_of_finiteDimensional F b',
      normalizedTraceAux_eq_of_finiteDimensional F ab',
      ← smul_add, ← map_add, AddMemClass.mk_add_mk]
  map_smul' m a := by
    dsimp only [AddHom.toFun_eq_coe, AddHom.coe_mk, RingHom.id_apply]
    let E := F⟮a⟯
    have : FiniteDimensional F F⟮a⟯ := adjoin.finiteDimensional (IsIntegral.isIntegral a)
    have ha : a ∈ E := mem_adjoin_simple_self F a
    have hma : m • a ∈ E := smul_mem E ha
    let a' : E := ⟨a, ha⟩
    let ma' : E := ⟨m • a, hma⟩
    rw [normalizedTraceAux_intermediateField F K a',
      normalizedTraceAux_intermediateField F K ma',
      normalizedTraceAux_eq_of_finiteDimensional F a',
      normalizedTraceAux_eq_of_finiteDimensional F ma',
      smul_comm, ← map_smul _ m, SetLike.mk_smul_mk]
/-
**Algebra.normalizedTrace_def** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：normalizedTrace_def (a : K) : normalizedTrace F K a = (Module.finrank F F⟮
a⟯ : F)⁻¹ • trace F F⟮a⟯ (AdjoinSimple.gen F a)
参数：a : K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem normalizedTrace_def (a : K) : normalizedTrace F K a =
    (Module.finrank F F⟮a⟯ : F)⁻¹ • trace F F⟮a⟯ (AdjoinSimple.gen F a) :=
  rfl

variable {K} in
/-- Normalized trace defined purely in terms of the degree and the next coefficient of the minimal
polynomial. Could be an alternative definition but it is harder to work with linearity. -/
/-
**Algebra.normalizedTrace_minpoly** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：normalizedTrace_minpoly (a : K) : normalizedTrace F K a = ((minpoly F a).n
atDegree : F)⁻¹ • -(minpoly F a).nextCoeff
参数：a : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `Algebra.normalizedTrace_def`：normalizedTrace_def (a : K) : normalizedTra
ce F K a = (Module.finrank F F⟮a⟯ : F)⁻¹ • trace F F⟮a⟯ (AdjoinSimple.gen F a)
· 使用定理 `trace_adjoinSimpleGen`：trace_adjoinSimpleGen {x : L} (hx : IsIntegral K 
x) : trace K K⟮x⟯ (AdjoinSimple.gen K x) = -(minpoly K x).nextCoeff
· 使用定理 `IntermediateField.adjoin.finrank`：∀ {K : Type u} [inst : Field K] {L : T
ype u_3} [inst_1 : Field L] [inst_2 : Algebra K L] {x : L},   IsIntegral K x → M
odule.finrank K ↥K⟮x⟯ …

--- 原说明 ---
Normalized trace defined purely in terms of the degree and the next coefficient 
of the minimal
polynomial. Could be an alternative definition but it is harder to work with lin
earity.
-/
theorem normalizedTrace_minpoly (a : K) :
    normalizedTrace F K a = ((minpoly F a).natDegree : F)⁻¹ • -(minpoly F a).nextCoeff :=
  have ha : IsIntegral F a := IsIntegral.isIntegral a
  IntermediateField.adjoin.finrank ha ▸ trace_adjoinSimpleGen ha ▸ normalizedTrace_def F K a

variable {F} in
/-
**Algebra.normalizedTrace_self_apply** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：normalizedTrace_self_apply (a : F) : normalizedTrace F F a = a
参数：a : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPurelyInseparable.isIntegral`：∀ {F : Type u_1} {E : Type u_2} {inst : 
CommRing F} {inst_1 : Ring E} {inst_2 : Algebra F E}   [self : IsPurelyInseparab
le F E], Algebra.IsI…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.FieldTheory.NormalizedTrace.0.Algebra.normalizedTraceAu
x_eq_of_finiteDimensional`：∀ (F : Type u_1) {K : Type u_2} [inst : Field F] [ins
t_1 : Field K] [inst_2 : Algebra F K] [CharZero F]   [FiniteDimensional F K] (a 
: K), A…
· 使用定理 `Module.finrank_self`：finrank_self : finrank R R = 1
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Algebra.trace_self_apply`：trace_self_apply (a) : trace R R a = a
-/
theorem normalizedTrace_self_apply (a : F) : normalizedTrace F F a = a := by
  dsimp [normalizedTrace]
  rw [normalizedTraceAux_eq_of_finiteDimensional F a, Module.finrank_self F,
    Nat.cast_one, inv_one, one_smul, trace_self_apply]

@[simp]
/-
**Algebra.normalizedTrace_self** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：normalizedTrace_self : normalizedTrace F F = LinearMap.id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsPurelyInseparable.isIntegral`：∀ {F : Type u_1} {E : Type u_2} {inst : 
CommRing F} {inst_1 : Ring E} {inst_2 : Algebra F E}   [self : IsPurelyInseparab
le F E], Algebra.IsI…
· 使用定理 `Algebra.normalizedTrace_self_apply`：normalizedTrace_self_apply (a : F) :
 normalizedTrace F F a = a
-/
theorem normalizedTrace_self : normalizedTrace F F = LinearMap.id :=
  LinearMap.ext normalizedTrace_self_apply

variable {K} in
/-
**Algebra.normalizedTrace_eq_of_finiteDimensional_apply** 是 Mathlib 中的一个定理，位于命名空
间 `Algebra`。
形式化陈述：normalizedTrace_eq_of_finiteDimensional_apply [FiniteDimensional F K] (a :
 K) : normalizedTrace F K a = (Module.finrank F K : F)⁻¹ • trace F K a
参数：a : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.FieldTheory.NormalizedTrace.0.Algebra.normalizedTraceAu
x_eq_of_finiteDimensional`：∀ (F : Type u_1) {K : Type u_2} [inst : Field F] [ins
t_1 : Field K] [inst_2 : Algebra F K] [CharZero F]   [FiniteDimensional F K] (a 
: K), A…
-/
theorem normalizedTrace_eq_of_finiteDimensional_apply [FiniteDimensional F K] (a : K) :
    normalizedTrace F K a = (Module.finrank F K : F)⁻¹ • trace F K a :=
  normalizedTraceAux_eq_of_finiteDimensional F a
/-
**Algebra.normalizedTrace_eq_of_finiteDimensional** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebra`。
形式化陈述：normalizedTrace_eq_of_finiteDimensional [FiniteDimensional F K] : normaliz
edTrace F K = (Module.finrank F K : F)⁻¹ • trace F K
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.normalizedTrace_eq_of_finiteDimensional_apply`：normalizedTrace_e
q_of_finiteDimensional_apply [FiniteDimensional F K] (a : K) : normalizedTrace F
 K a = (Module.finrank F K : F)⁻¹ • trace F…
-/
theorem normalizedTrace_eq_of_finiteDimensional [FiniteDimensional F K] :
    normalizedTrace F K = (Module.finrank F K : F)⁻¹ • trace F K :=
  LinearMap.ext <| normalizedTrace_eq_of_finiteDimensional_apply F

/-- The normalized trace transfers via (injective) maps. -/
@[simp]
/-
**Algebra.normalizedTrace_map** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：normalizedTrace_map {E : Type*} [Field E] [Algebra F E] [Algebra.IsIntegra
l F E] (f : E ->ₐ[F] K) (a : E) : normalizedTrace F K (f a) = normalizedTrace F 
E a
参数：f : E ->ₐ[F] K；a : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.FieldTheory.NormalizedTrace.0.Algebra.normalizedTraceAu
x_map`：∀ (F : Type u_1) (K : Type u_2) [inst : Field F] [inst_1 : Field K] [inst
_2 : Algebra F K] {E : Type u_3}   [inst_3 : Field E] [inst_4 : Alg…

--- 原说明 ---
The normalized trace transfers via (injective) maps.
-/
theorem normalizedTrace_map {E : Type*} [Field E] [Algebra F E] [Algebra.IsIntegral F E]
    (f : E →ₐ[F] K) (a : E) : normalizedTrace F K (f a) = normalizedTrace F E a :=
  normalizedTraceAux_map F K f a

/-- The normalized trace transfers via restriction to a subextension. -/
/-
**Algebra.normalizedTrace_intermediateField** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：normalizedTrace_intermediateField {E : IntermediateField F K} (a : E) : no
rmalizedTrace F K a = normalizedTrace F E a
参数：a : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.FieldTheory.NormalizedTrace.0.Algebra.normalizedTraceAu
x_intermediateField`：∀ (F : Type u_1) (K : Type u_2) [inst : Field F] [inst_1 : 
Field K] [inst_2 : Algebra F K] {E : IntermediateField F K}   (a : ↥E), Algebra.
n…

--- 原说明 ---
The normalized trace transfers via restriction to a subextension.
-/
theorem normalizedTrace_intermediateField {E : IntermediateField F K} (a : E) :
    normalizedTrace F K a = normalizedTrace F E a :=
  normalizedTraceAux_intermediateField F K a

section IsScalarTower

variable (F E K : Type*) [Field F] [Field E] [Field K]
variable [Algebra F E] [Algebra E K] [Algebra F K] [IsScalarTower F E K]
variable [Algebra.IsIntegral F E] [Algebra.IsIntegral F K]
variable [CharZero F]

@[simp]
/-
**Algebra.normalizedTrace_algebraMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：normalizedTrace_algebraMap_apply (a : E) : normalizedTrace F K (algebraMap
 E K a) = normalizedTrace F E a
参数：a : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.normalizedTrace_map`：normalizedTrace_map {E : Type*} [Field E] [
Algebra F E] [Algebra.IsIntegral F E] (f : E ->ₐ[F] K) (a : E) : normalizedTrace
 F K (f a) = norm…
-/
theorem normalizedTrace_algebraMap_apply (a : E) :
    normalizedTrace F K (algebraMap E K a) = normalizedTrace F E a :=
  normalizedTrace_map F K (IsScalarTower.toAlgHom F E K) a

@[simp]
/-
**Algebra.normalizedTrace_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：normalizedTrace_algebraMap : normalizedTrace F K ∘ₗ Algebra.linearMap E K 
= normalizedTrace F E
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul'`：∀ {M : Type u_8} [inst : AddCom
mMonoid M] {R : Type u_14} {S : Type u_15} [inst_1 : Semiring S] [inst_2 : SMul 
R M]   [inst_3 : _root_.Modul…
· 使用定理 `Algebra.normalizedTrace_algebraMap_apply`：normalizedTrace_algebraMap_app
ly (a : E) : normalizedTrace F K (algebraMap E K a) = normalizedTrace F E a
-/
theorem normalizedTrace_algebraMap :
    normalizedTrace F K ∘ₗ Algebra.linearMap E K = normalizedTrace F E :=
  LinearMap.ext <| normalizedTrace_algebraMap_apply F E K

omit [Algebra.IsIntegral F E] in
/-- If all the coefficients of `minpoly E a` are in `F`, then the normalized trace of `a` from `K`
to `E` equals the normalized trace of `a` from `K` to `F`. -/
/-
**Algebra.normalizedTrace_algebraMap_of_lifts** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
`。
形式化陈述：normalizedTrace_algebraMap_of_lifts [CharZero E] [Algebra.IsIntegral E K] 
(a : K) (h : minpoly E a in Polynomial.lifts (algebraMap F E)) : algebraMap F E 
(normalizedTrace F K a) = normalizedTrace E K a
参数：a : K；h : minpoly E a in Polynomial.lifts (algebraMap F E)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.normalizedTrace_minpoly`：normalizedTrace_minpoly (a : K) : norma
lizedTrace F K a = ((minpoly F a).natDegree : F)⁻¹ • -(minpoly F a).nextCoeff
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `minpoly.map_algebraMap`：map_algebraMap {F E A : Type*} [Field F] [Field 
E] [CommRing A] [Algebra F E] [Algebra E A] [Algebra F A] [IsScalarTower F E A] 
{a : A} (ha …
· 使用定理 `Polynomial.natDegree_map`：natDegree_map (f : R ->+* S) : (p.map f).natDe
gree = p.natDegree
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Polynomial.nextCoeff_map_eq`：nextCoeff_map_eq (p : R[X]) (f : R ->+* S) 
: (p.map f).nextCoeff = f p.nextCoeff
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If all the coefficients of `minpoly E a` are in `F`, then the normalized trace o
f `a` from `K`
to `E` equals the normalized trace of `a` from `K` to `F`.
-/
theorem normalizedTrace_algebraMap_of_lifts [CharZero E] [Algebra.IsIntegral E K] (a : K)
    (h : minpoly E a ∈ Polynomial.lifts (algebraMap F E)) :
    algebraMap F E (normalizedTrace F K a) = normalizedTrace E K a := by
  have ha : IsIntegral F a := IsIntegral.isIntegral a
  simp [normalizedTrace_minpoly F a, normalizedTrace_minpoly E a, ← minpoly.map_algebraMap ha h,
    (minpoly F a).nextCoeff_map_eq, map_mul, map_neg]

set_option backward.isDefEq.respectTransparency false in
/- An auxiliary result to prove `normalizedTrace_trans_apply`. It differs from
`normalizedTrace_trans_apply` only by the extra assumption about finiteness of `E` over `F`. -/
/-
**Algebra.normalizedTrace_trans_apply_aux** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary result to prove `normalizedTrace_trans_apply`. It differs from
`normalizedTrace_trans_apply` only by the extra assumption about finiteness of `
E` over `F`.
-/
private theorem normalizedTrace_trans_apply_aux [FiniteDimensional F E] [Algebra.IsIntegral E K]
    [CharZero E] (a : K) :
    normalizedTrace F E (normalizedTrace E K a) = normalizedTrace F K a := by
  have : FiniteDimensional E E⟮a⟯ :=
    IntermediateField.adjoin.finiteDimensional (IsIntegral.isIntegral a)
  rw [normalizedTrace_def E K, inv_natCast_smul_eq (R := E) (S := F), map_smul,
    normalizedTrace_eq_of_finiteDimensional F E, LinearMap.smul_apply, ← smul_assoc,
    smul_eq_mul (a := _⁻¹), ← mul_inv, trace_trace, mul_comm,
    ← Nat.cast_mul, Module.finrank_mul_finrank, eq_comm]
  let E' := E⟮a⟯.restrictScalars F
  have : FiniteDimensional F E' := Module.Finite.trans E E⟮a⟯
  have h_finrank_eq : Module.finrank F E⟮a⟯ = Module.finrank F E' := rfl
  have h_trace_eq : trace F E⟮a⟯ (AdjoinSimple.gen E a) = trace F E' (AdjoinSimple.gen E a : E') :=
    rfl
  let a' : E' := AdjoinSimple.gen E a
  rw [h_finrank_eq, h_trace_eq, ← normalizedTrace_eq_of_finiteDimensional_apply F,
    ← normalizedTrace_intermediateField F K a']
  congr

/-- For a tower `K / E / F` of algebraic extensions, the normalized trace from `K` to `E` composed
with the normalized trace from `E` to `F` equals the normalized trace from `K` to `F`. -/
/-
**Algebra.normalizedTrace_trans_apply** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：normalizedTrace_trans_apply [Algebra.IsIntegral E K] [CharZero E] (a : K) 
: normalizedTrace F E (normalizedTrace E K a) = normalizedTrace F K a
参数：a : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.finiteDimensional_adjoin`：finiteDimensional_adjoin {S 
: Set L} [Finite S] (hS : forall x in S, IsIntegral K x) : FiniteDimensional K (
adjoin K S)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `Algebra.IsIntegral.tower_top`：Algebra.IsIntegral.tower_top [Algebra R S]
 [Algebra R T] [Algebra S T] [IsScalarTower R S T] [h : Algebra.IsIntegral R T] 
: Algebra.IsIntegr…
· 使用定理 `Algebra.IsIntegral.trans`：∀ {R : Type u_1} (A : Type u_2) {B : Type u_3}
 [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Ring B]   [inst_3 : Algebra
 A B] [inst_4 …
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IntermediateField.subset_adjoin`：subset_adjoin : S subseteq adjoin F S
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subalgebra.range_algebraMap`：range_algebraMap {R A : Type*} [CommRing R]
 [CommRing A] [Algebra R A] (S : Subalgebra R A) : (algebraMap S A).range = S.to
Subring
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.lifts_iff_coeffs_subset_range`：lifts_iff_coeffs_subset_range 
(p : S[X]) : p in lifts f ↔ (p.coeffs : Set S) subseteq Set.range f
· 使用定理 `Algebra.IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Fiel
d K] [inst_1 : Ring A] [inst_2 : Algebra K A] [Algebra.IsAlgebraic K A],   Algeb
ra.IsIntegral K A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Algebra.IsSeparable.of_integral`：∀ (F : Type u_1) [inst : Field F] (K : 
Type u_2) [inst_1 : Ring K] [inst_2 : Algebra F K] [IsDomain K]   [Algebra.IsInt
egral F K] [CharZero …
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.normalizedTrace_algebraMap_of_lifts`：normalizedTrace_algebraMap_
of_lifts [CharZero E] [Algebra.IsIntegral E K] (a : K) (h : minpoly E a in Polyn
omial.lifts (algebraMap F E)) : a…
· 使用定理 `Algebra.normalizedTrace_algebraMap_apply`：normalizedTrace_algebraMap_app
ly (a : E) : normalizedTrace F K (algebraMap E K a) = normalizedTrace F E a
· 使用定理 `_private.Mathlib.FieldTheory.NormalizedTrace.0.Algebra.normalizedTrace_t
rans_apply_aux`：∀ (F : Type u_3) (E : Type u_4) (K : Type u_5) [inst : Field F] 
[inst_1 : Field E] [inst_2 : Field K]   [inst_3 : Algebra F E] [inst_4 : Alg…

--- 原说明 ---
For a tower `K / E / F` of algebraic extensions, the normalized trace from `K` t
o `E` composed
with the normalized trace from `E` to `F` equals the normalized trace from `K` t
o `F`.
-/
theorem normalizedTrace_trans_apply [Algebra.IsIntegral E K] [CharZero E] (a : K) :
    normalizedTrace F E (normalizedTrace E K a) = normalizedTrace F K a :=
  let S : Set E := (minpoly E a).coeffs
  let E₀ := IntermediateField.adjoin F S
  have : FiniteDimensional F E₀ := IntermediateField.finiteDimensional_adjoin
    fun x _ ↦ Algebra.IsIntegral.isIntegral x
  have : Algebra.IsIntegral E₀ E := IsIntegral.tower_top F
  have : Algebra.IsIntegral E₀ K := IsIntegral.trans E
  have hsub : S ⊆ (algebraMap E₀ E).range :=
    Subalgebra.range_algebraMap E₀.toSubalgebra ▸ IntermediateField.subset_adjoin F S
  have hlifts := (Polynomial.lifts_iff_coeffs_subset_range _).mpr hsub
  (normalizedTrace_trans_apply_aux F E₀ K _ ▸
    normalizedTrace_algebraMap_apply F E₀ E _ ▸
    congrArg (normalizedTrace F E) (normalizedTrace_algebraMap_of_lifts E₀ E K a hlifts)).symm

@[simp]
/-
**Algebra.normalizedTrace_trans** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：normalizedTrace_trans [Algebra.IsIntegral E K] [CharZero E] : normalizedTr
ace F E ∘ₗ normalizedTrace E K = normalizedTrace F K
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.normalizedTrace_trans_apply`：normalizedTrace_trans_apply [Algebr
a.IsIntegral E K] [CharZero E] (a : K) : normalizedTrace F E (normalizedTrace E 
K a) = normalizedTrace F …
-/
theorem normalizedTrace_trans [Algebra.IsIntegral E K] [CharZero E] :
    normalizedTrace F E ∘ₗ normalizedTrace E K = normalizedTrace F K :=
  LinearMap.ext <| normalizedTrace_trans_apply F E K

end IsScalarTower

/-
**Algebra.normalizedTrace_algebraMap_apply_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Al
gebra`。
形式化陈述：normalizedTrace_algebraMap_apply_eq_self (a : F) : normalizedTrace F K (al
gebraMap F K a) = a
参数：a : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsPurelyInseparable.isIntegral`：∀ {F : Type u_1} {E : Type u_2} {inst : 
CommRing F} {inst_1 : Ring E} {inst_2 : Algebra F E}   [self : IsPurelyInseparab
le F E], Algebra.IsI…
· 使用定理 `Algebra.normalizedTrace_algebraMap_apply`：normalizedTrace_algebraMap_app
ly (a : E) : normalizedTrace F K (algebraMap E K a) = normalizedTrace F E a
· 使用定理 `Algebra.normalizedTrace_self`：normalizedTrace_self : normalizedTrace F F
 = LinearMap.id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem normalizedTrace_algebraMap_apply_eq_self (a : F) :
    normalizedTrace F K (algebraMap F K a) = a := by simp

/-- The normalized trace map is a left inverse of the algebra map. -/
/-
**Algebra.normalizedTrace_algebraMap_eq_id** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：normalizedTrace_algebraMap_eq_id : normalizedTrace F K ∘ₗ Algebra.linearMa
p F K = LinearMap.id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Algebra.normalizedTrace_algebraMap_apply_eq_self`：normalizedTrace_algebr
aMap_apply_eq_self (a : F) : normalizedTrace F K (algebraMap F K a) = a

--- 原说明 ---
The normalized trace map is a left inverse of the algebra map.
-/
theorem normalizedTrace_algebraMap_eq_id :
    normalizedTrace F K ∘ₗ Algebra.linearMap F K = LinearMap.id :=
  LinearMap.ext <| normalizedTrace_algebraMap_apply_eq_self F K

/-- The normalized trace commutes with (injective) maps. -/
@[simp]
/-
**Algebra.normalizedTrace_comp_algHom** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：normalizedTrace_comp_algHom {E : Type*} [Field E] [Algebra F E] [Algebra.I
sIntegral F E] (f : E ->ₐ[F] K) : normalizedTrace F K ∘ₗ f = normalizedTrace F E
参数：f : E ->ₐ[F] K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `Algebra.normalizedTrace_map`：normalizedTrace_map {E : Type*} [Field E] [
Algebra F E] [Algebra.IsIntegral F E] (f : E ->ₐ[F] K) (a : E) : normalizedTrace
 F K (f a) = norm…

--- 原说明 ---
The normalized trace commutes with (injective) maps.
-/
theorem normalizedTrace_comp_algHom {E : Type*} [Field E] [Algebra F E] [Algebra.IsIntegral F E]
    (f : E →ₐ[F] K) : normalizedTrace F K ∘ₗ f = normalizedTrace F E :=
  LinearMap.ext <| normalizedTrace_map F K f
/-
**Algebra.normalizedTrace_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：normalizedTrace_surjective : Function.Surjective (normalizedTrace F K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.normalizedTrace_algebraMap_apply_eq_self`：normalizedTrace_algebr
aMap_apply_eq_self (a : F) : normalizedTrace F K (algebraMap F K a) = a
-/
theorem normalizedTrace_surjective : Function.Surjective (normalizedTrace F K) :=
  fun a ↦ ⟨algebraMap F K a, normalizedTrace_algebraMap_apply_eq_self F K a⟩

/-- The normalized trace map is non-trivial. -/
/-
**Algebra.normalizedTrace_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：normalizedTrace_ne_zero : normalizedTrace F K != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.normalizedTrace_surjective`：normalizedTrace_surjective : Functio
n.Surjective (normalizedTrace F K)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `DFunLike.ne_iff`：ne_iff {f g : F} : f != g ↔ exists a, f a != g a
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The normalized trace map is non-trivial.
-/
theorem normalizedTrace_ne_zero : normalizedTrace F K ≠ 0 :=
  let ⟨a, ha⟩ := normalizedTrace_surjective F K 1
  DFunLike.ne_iff.mpr <| ⟨a, ha ▸ one_ne_zero⟩

end Algebra

