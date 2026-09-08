/-
Copyright (c) 2025 Yong-Gyu Choi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yong-Gyu Choi
-/
module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Exactness properties of the difference map on tensor products

For an `R`-algebra `S`, we collect some properties of the `R`-linear map `S →ₗ[R] S ⊗[R] S` given
by `s ↦ s ⊗ₜ 1 - 1 ⊗ₜ s`.

## Main definitions

* `includeLeftSubRight`: The `R`-linear map sending `s : S` to `s ⊗ₜ 1 - 1 ⊗ₜ s`.
* `IsEffective`: Exactness of the sequence `R → S → S ⊗[R] S` where the first map is
  `Algebra.linearMap R S` and the second map is `includeLeftSubRight`. When `R` and `S` are
  commutative rings, this is equivalent to the inclusion `im (algebraMap : R → S) → S` being an
  effective monomorphism in `CommRingCat`.

## Main results

* `IsEffective.of_faithfullyFlat`: `IsEffective R S` is true for any faithfully flat `R`-algebra `S`

-/

@[expose] public section

open scoped TensorProduct

namespace Algebra

variable {R : Type*} [CommSemiring R]
variable {S : Type*} [Ring S] [Algebra R S]

namespace TensorProduct

section IncludeLeftSubRight

variable (R S) in
/-- The `R`-linear map `S →ₗ[R] S ⊗[R] S` sending `s : S` to `s ⊗ₜ 1 - 1 ⊗ₜ s`. -/
/-
**Algebra.TensorProduct.includeLeftSubRight** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.T
ensorProduct`。
形式化陈述：includeLeftSubRight : S ->ₗ[R] S otimes[R] S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `R`-linear map `S →ₗ[R] S ⊗[R] S` sending `s : S` to `s ⊗ₜ 1 - 1 ⊗ₜ s`.
-/
def includeLeftSubRight : S →ₗ[R] S ⊗[R] S :=
  includeLeft.toLinearMap - includeRight.toLinearMap

@[simp]
/-
**Algebra.TensorProduct.includeLeftSubRight_apply** 是 Mathlib 中的一个引理，位于命名空间 `Alg
ebra.TensorProduct`。
形式化陈述：includeLeftSubRight_apply (s : S) : includeLeftSubRight R S s = s otimesₜ[
R] 1 - 1 otimesₜ[R] s
参数：s : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma includeLeftSubRight_apply (s : S) : includeLeftSubRight R S s = s ⊗ₜ[R] 1 - 1 ⊗ₜ[R] s :=
  rfl

/-- `includeLeftSubRight R S` vanishes in the range of `algebraMap R S`. -/
/-
**Algebra.TensorProduct.includeLeftSubRight_zero_of_mem_range** 是 Mathlib 中的一个引理
，位于命名空间 `Algebra.TensorProduct`。
形式化陈述：includeLeftSubRight_zero_of_mem_range {s : S} (hs : s in Set.range ⇑(algeb
raMap R S)) : includeLeftSubRight R S s = 0
参数：hs : s in Set.range ⇑(algebraMap R S)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`includeLeftSubRight R S` vanishes in the range of `algebraMap R S`.
-/
lemma includeLeftSubRight_zero_of_mem_range {s : S} (hs : s ∈ Set.range ⇑(algebraMap R S)) :
    includeLeftSubRight R S s = 0 := by
  obtain ⟨_, hr⟩ := Set.mem_range.mp hs
  simp [← hr, algebraMap_eq_smul_one]

/-- `includeLeftSubRight R S` vanishes at `algebraMap R S r`. -/
/-
**Algebra.TensorProduct.includeLeftSubRight_algebraMap_zero** 是 Mathlib 中的一个引理，位
于命名空间 `Algebra.TensorProduct`。
形式化陈述：includeLeftSubRight_algebraMap_zero (r : R) : includeLeftSubRight R S (alg
ebraMap R S r) = 0
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.TensorProduct.includeLeftSubRight_zero_of_mem_range`：includeLeft
SubRight_zero_of_mem_range {s : S} (hs : s in Set.range ⇑(algebraMap R S)) : inc
ludeLeftSubRight R S s = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
· 使用定理 `exists_apply_eq_apply`：∀ {α : Sort u_2} {β : Sort u_1} (f : α → β) (a' :
 α), ∃ a, f a = f a'

--- 原说明 ---
`includeLeftSubRight R S` vanishes at `algebraMap R S r`.
-/
lemma includeLeftSubRight_algebraMap_zero (r : R) :
    includeLeftSubRight R S (algebraMap R S r) = 0 :=
  includeLeftSubRight_zero_of_mem_range (Set.mem_range.mp (exists_apply_eq_apply _ _))

/-- `includeLeftSubRight` is compatible with `distribBaseChange` and `lTensor`. -/
/-
**Algebra.TensorProduct.distribBaseChange_comp_includeLeftSubRight** 是 Mathlib 中
的一个引理，位于命名空间 `Algebra.TensorProduct`。
形式化陈述：distribBaseChange_comp_includeLeftSubRight (T : Type*) [CommRing T] [Algeb
ra R T] : ((TensorProduct.AlgebraTensorModule.distribBaseChange R T S S).restric
tScalars R).toLinearMap ∘ₗ (includeLeftSubRight R S).lTensor T = (includeLeftSub
Right T (T otimes[R] S)).restrictScalars R
参数：T : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
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
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `LinearEquiv.restrictScalars_toLinearMap`：∀ (R : Type u_1) {S : Type u_4}
 {M : Type u_5} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring S]   [ins
t_2 : AddCommMonoid M] [inst_…
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `TensorProduct.tmul_sub`：tmul_sub (m : M) (p₁ p₂ : P) : m otimesₜ (p₁ - p
₂) = m otimesₜ[R] p₁ - m otimesₜ[R] p₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
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
· 使用引理 `Algebra.TensorProduct.tmul_one_tmul_one_tmul`：tmul_one_tmul_one_tmul (x 
: A) (y : C) : x otimesₜ[R] (1 : B) otimesₜ[A] ((1 : A) otimesₜ[R] y) = 1 otimes
ₜ[A] (x otimesₜ[R] y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`includeLeftSubRight` is compatible with `distribBaseChange` and `lTensor`.
-/
lemma distribBaseChange_comp_includeLeftSubRight (T : Type*) [CommRing T] [Algebra R T] :
    ((TensorProduct.AlgebraTensorModule.distribBaseChange R T S S).restrictScalars R).toLinearMap ∘ₗ
      (includeLeftSubRight R S).lTensor T =
    (includeLeftSubRight T (T ⊗[R] S)).restrictScalars R := by
  ext
  simp [TensorProduct.tmul_sub, TensorProduct.one_def, tmul_one_tmul_one_tmul]

@[simp]
/-
**Algebra.TensorProduct.distribBaseChange_includeLeftSubRight_apply** 是 Mathlib 
中的一个引理，位于命名空间 `Algebra.TensorProduct`。
形式化陈述：distribBaseChange_includeLeftSubRight_apply (T : Type*) [CommRing T] [Alge
bra R T] (x : T otimes[R] S) : TensorProduct.AlgebraTensorModule.distribBaseChan
ge R T S S ((includeLeftSubRight R S).lTensor T x) = includeLeftSubRight T (T ot
imes[R] S) x
参数：T : Type*；x : T otimes[R] S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用引理 `Algebra.TensorProduct.distribBaseChange_comp_includeLeftSubRight`：distri
bBaseChange_comp_includeLeftSubRight (T : Type*) [CommRing T] [Algebra R T] : ((
TensorProduct.AlgebraTensorModule.distribBaseChange R …
-/
lemma distribBaseChange_includeLeftSubRight_apply (T : Type*) [CommRing T] [Algebra R T]
    (x : T ⊗[R] S) :
    TensorProduct.AlgebraTensorModule.distribBaseChange R T S S
      ((includeLeftSubRight R S).lTensor T x) =
    includeLeftSubRight T (T ⊗[R] S) x :=
  congr($(distribBaseChange_comp_includeLeftSubRight _) x)

end IncludeLeftSubRight

end TensorProduct

variable (R S) in
/-- For an `R`-algebra `S`, this asserts that the maps `algebraMap : R → S` and
`includeLeftSubRight R S : S → S ⊗[R] S` form an exact pair.
When `R` and `S` are commutative rings, this is true if and only if the inclusion
`im (algebraMap : R → S) → S` is an effective monomorphism in the category of commutative rings. -/
/-
**Algebra.IsEffective** 是 Mathlib 中的一个定义，位于命名空间 `Algebra`。
形式化陈述：IsEffective : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For an `R`-algebra `S`, this asserts that the maps `algebraMap : R → S` and
`includeLeftSubRight R S : S → S ⊗[R] S` form an exact pair.
When `R` and `S` are commutative rings, this is true if and only if the inclusio
n
`im (algebraMap : R → S) → S` is an effective monomorphism in the category of co
mmutative rings.
-/
def IsEffective : Prop :=
  Function.Exact (Algebra.linearMap R S) (TensorProduct.includeLeftSubRight R S)

namespace IsEffective

/-- If `IsEffective R S` is true, then the equalizer of `s ↦ s ⊗ₜ 1 : S →+* S ⊗[R] S` and
`s ↦ 1 ⊗ₜ s : S →+* S ⊗[R] S` is the image of `algebraMap R S : R →+* S`. -/
/-
**Algebra.IsEffective.eqLocus_includeLeft_includeRight** 是 Mathlib 中的一个引理，位于命名空间
 `Algebra.IsEffective`。
形式化陈述：eqLocus_includeLeft_includeRight (h : IsEffective R S) : TensorProduct.inc
ludeLeftRingHom.eqLocus TensorProduct.includeRight.toRingHom (S
参数：h : IsEffective R S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Algebra.TensorProduct.includeLeftSubRight_apply`：includeLeftSubRight_app
ly (s : S) : includeLeftSubRight R S s = s otimesₜ[R] 1 - 1 otimesₜ[R] s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Algebra.TensorProduct.includeLeftRingHom_apply`：∀ {R : Type uR} {A : Typ
e uA} {B : Type uB} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Alge
bra R A]   [inst_3 : Semiring B] [in…
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `IsEffective R S` is true, then the equalizer of `s ↦ s ⊗ₜ 1 : S →+* S ⊗[R] S
` and
`s ↦ 1 ⊗ₜ s : S →+* S ⊗[R] S` is the image of `algebraMap R S : R →+* S`.
-/
lemma eqLocus_includeLeft_includeRight (h : IsEffective R S) :
    TensorProduct.includeLeftRingHom.eqLocus TensorProduct.includeRight.toRingHom (S := S ⊗[R] S) =
      Set.range (algebraMap R S) := by
  ext s
  refine ⟨?_, fun ⟨_, hr⟩ ↦ by simp [← hr]⟩
  intro hs
  exact (h s).mp <| (TensorProduct.includeLeftSubRight_apply (R := R) s).symm ▸ sub_eq_zero.mpr hs

/-- `IsEffective` is true for any `R`-algebra `S` having an `R`-algebra section of
`Algebra.ofId _ _ : R →ₐ[R] S`. -/
/-
**Algebra.IsEffective.of_section** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.IsEffective`
。
形式化陈述：of_section (g : S ->ₐ[R] R) : IsEffective R S
参数：g : S ->ₐ[R] R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.injective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.TensorProduct.lid_symm_apply`：lid_symm_apply (a : A) : (TensorPr
oduct.lid R A).symm a = 1 otimesₜ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Algebra.coe_linearMap`：coe_linearMap : ⇑(Algebra.linearMap R A) = algebr
aMap R A
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `TensorProduct.smul_tmul`：smul_tmul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (m : M) (n : N) : (r • m) otimesₜ n = m otimesₜ[R] (r • n)
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `AlgHom.id_apply`：id_apply (p : A) : AlgHom.id R A p = p
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Algebra.TensorProduct.map_tmul`：map_tmul (f : A ->ₐ[S] C) (g : B ->ₐ[R] 
D) (a : A) (b : B) : map f g (a otimesₜ b) = f a otimesₜ g b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Algebra.TensorProduct.includeLeftSubRight_apply`：includeLeftSubRight_app
ly (s : S) : includeLeftSubRight R S s = s otimesₜ[R] 1 - 1 otimesₜ[R] s
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
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用引理 `Algebra.TensorProduct.includeLeftSubRight_zero_of_mem_range`：includeLeft
SubRight_zero_of_mem_range {s : S} (hs : s in Set.range ⇑(algebraMap R S)) : inc
ludeLeftSubRight R S s = 0

--- 原说明 ---
`IsEffective` is true for any `R`-algebra `S` having an `R`-algebra section of
`Algebra.ofId _ _ : R →ₐ[R] S`.
-/
lemma of_section (g : S →ₐ[R] R) : IsEffective R S := by
  intro s
  refine ⟨?_, TensorProduct.includeLeftSubRight_zero_of_mem_range⟩
  intro hs
  use g s
  apply (TensorProduct.lid R S).symm.injective
  rw [TensorProduct.lid_symm_apply, TensorProduct.lid_symm_apply,
    ← mul_one ((Algebra.linearMap R S) _), Algebra.coe_linearMap, ← Algebra.smul_def,
    ← TensorProduct.smul_tmul, smul_eq_mul, mul_one, ← AlgHom.id_apply (R := R) (1 : S),
    ← TensorProduct.map_tmul,
    sub_eq_zero.mp ((TensorProduct.includeLeftSubRight_apply s).symm.trans hs),
    TensorProduct.map_tmul, map_one, AlgHom.id_apply]

section FaithfullyFlat

variable (R : Type*) [CommRing R]
variable (S : Type*)
variable (T : Type*) [CommRing T] [Algebra R T]

/-- `IsEffective` descends along faithfully flat algebras. -/
/-
**Algebra.IsEffective.of_isEffective_tensorProduct_of_faithfullyFlat** 是 Mathlib
 中的一个引理，位于命名空间 `Algebra.IsEffective`。
形式化陈述：of_isEffective_tensorProduct_of_faithfullyFlat [Ring S] [Algebra R S] [Mod
ule.FaithfullyFlat R T] (h : IsEffective T (T otimes[R] S)) : IsEffective R S
参数：h : IsEffective T (T otimes[R] S)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `Module.FaithfullyFlat.lTensor_reflects_exact`：lTensor_reflects_exact [fl
 : FaithfullyFlat R M] (ex : Function.Exact (l12.lTensor M) (l23.lTensor M)) : F
unction.Exact l12 l23
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `AddMonoidHom.exact_iff_of_surjective_of_bijective_of_injective`：∀ {M₁ : 
Type u_8} {M₂ : Type u_9} {M₃ : Type u_10} {N₁ : Type u_11} {N₂ : Type u_12} {N₃
 : Type u_13}   [inst : AddCommMonoid M₁] [inst_1 : …
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul'`：∀ {M : Type u_8} [inst : AddCom
mMonoid M] {R : Type u_14} {S : Type u_15} [inst_1 : Semiring S] [inst_2 : SMul 
R M]   [inst_3 : _root_.Modul…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AddMonoidHomClass.toAddMonoidHom.congr_simp`：∀ {M : Type u_4} {N : Type 
u_5} {F : Type u_9} [inst : AddZero M] [inst_1 : AddZero N] [inst_2 : FunLike F 
M N]   [inst_3 : AddMonoidHomClas…
· 使用定理 `AddMonoidHom.id_comp`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M]
 [inst_1 : AddZero N] (f : M →+ N), (AddMonoidHom.id N).comp f = f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AddMonoidHom.comp_id`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M]
 [inst_1 : AddZero N] (f : M →+ N), f.comp (AddMonoidHom.id M) = f
· 使用引理 `Algebra.TensorProduct.distribBaseChange_includeLeftSubRight_apply`：distr
ibBaseChange_includeLeftSubRight_apply (T : Type*) [CommRing T] [Algebra R T] (x
 : T otimes[R] S) : TensorProduct.AlgebraTensorModule.d…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AlgEquiv.surjective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [in
st : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : A
lgebra R …
· 使用定理 `Function.bijective_id`：bijective_id : Bijective (@id α)
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…

--- 原说明 ---
`IsEffective` descends along faithfully flat algebras.
-/
lemma of_isEffective_tensorProduct_of_faithfullyFlat
    [Ring S] [Algebra R S] [Module.FaithfullyFlat R T] (h : IsEffective T (T ⊗[R] S)) :
    IsEffective R S := by
  refine Module.FaithfullyFlat.lTensor_reflects_exact _ _ _ _ <|
    AddMonoidHom.exact_iff_of_surjective_of_bijective_of_injective
      ((Algebra.linearMap R S).lTensor T) ((TensorProduct.includeLeftSubRight R S).lTensor T)
      (Algebra.linearMap T (T ⊗[R] S)) (TensorProduct.includeLeftSubRight T (T ⊗[R] S))
      (TensorProduct.rid R R T).toAddMonoidHom (AddMonoidHom.id (T ⊗[R] S))
      (TensorProduct.AlgebraTensorModule.distribBaseChange R T S S).toAddMonoidHom ?_ ?_
      (TensorProduct.rid R R T).surjective Function.bijective_id
      ((TensorProduct.AlgebraTensorModule.distribBaseChange R T S S).injective) |>.mpr ‹_›
  · ext
    simp [← Algebra.TensorProduct.linearMap_comp_rid]
    -- The goal is TensorProduct.rid .. = TensorProduct.AlgebraTensorModule.rid ..
    -- TODO: merge both into one definition, and remove the rfl.
    rfl
  · ext
    simp

/-- `IsEffective R S` is true for any faithfully flat `R`-algebra `S`. -/
/-
**Algebra.IsEffective.of_faithfullyFlat** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.IsEff
ective`。
形式化陈述：of_faithfullyFlat [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S] :
 IsEffective R S
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.IsEffective.of_isEffective_tensorProduct_of_faithfullyFlat`：of_i
sEffective_tensorProduct_of_faithfullyFlat [Ring S] [Algebra R S] [Module.Faithf
ullyFlat R T] (h : IsEffective T (T otimes[R] S)) : IsEf…
· 使用引理 `Algebra.IsEffective.of_section`：of_section (g : S ->ₐ[R] R) : IsEffectiv
e R S
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A

--- 原说明 ---
`IsEffective R S` is true for any faithfully flat `R`-algebra `S`.
-/
lemma of_faithfullyFlat [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S] :
    IsEffective R S :=
  of_isEffective_tensorProduct_of_faithfullyFlat _ _ _ (of_section (TensorProduct.lmul'' R))

end FaithfullyFlat

end IsEffective

section CodRestrictEqLocusPushoutCocone

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical ring map from `R` to the explicit equalizer of
`includeLeft : S ⟶ S ⊗[R] S` and `includeRight : S ⟶ S ⊗[R] S`. -/
/-
**Algebra.codRestrictEqLocusPushoutCocone** 是 Mathlib 中的一个定义，位于命名空间 `Algebra`。
形式化陈述：codRestrictEqLocusPushoutCocone : R ->+* (CommRingCat.equalizerFork (CommR
ingCat.pushoutCocone R S S).inl (CommRingCat.pushoutCocone R S S).inr).pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical ring map from `R` to the explicit equalizer of
`includeLeft : S ⟶ S ⊗[R] S` and `includeRight : S ⟶ S ⊗[R] S`.
-/
def codRestrictEqLocusPushoutCocone :
    R →+* (CommRingCat.equalizerFork
      (CommRingCat.pushoutCocone R S S).inl (CommRingCat.pushoutCocone R S S).inr).pt :=
  RingHom.codRestrict (algebraMap R S)
    ((CommRingCat.pushoutCocone R S S).inl.hom.eqLocus (CommRingCat.pushoutCocone R S S).inr.hom)
    (by simp)

/-- Injectivity of `algebraMap R S` implies injectivity of `codRestrictEqLocusPushoutCocone`. -/
/-
**Algebra.codRestrictEqLocusPushoutCocone.injective_of_faithfulSMul** 是 Mathlib 
中的一个定理，位于命名空间 `Algebra.codRestrictEqLocusPushoutCocone`。
形式化陈述：∀ (R S : Type u) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algeb
ra R S] [FaithfulSMul R S],   Function.Injective ⇑(Algebra.codRestrictEqLocusPus
houtCocone R S)
参数：R S : Type u；Algebra.codRestrictEqLocusPushoutCocone R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `RingHom.injective_codRestrict`：injective_codRestrict {f : R ->+* S} {s :
 σS} {h : forall x, f x in s} : Function.Injective (f.codRestrict s h) ↔ Functio
n.Injective f
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)

--- 原说明 ---
Injectivity of `algebraMap R S` implies injectivity of `codRestrictEqLocusPushou
tCocone`.
-/
lemma codRestrictEqLocusPushoutCocone.injective_of_faithfulSMul [FaithfulSMul R S] :
    Function.Injective (codRestrictEqLocusPushoutCocone R S) :=
  RingHom.injective_codRestrict.mpr (FaithfulSMul.algebraMap_injective _ _)

/-- `Algebra.IsEffective R S` implies surjectivity of `codRestrictEqLocusPushoutCocone`. -/
/-
**Algebra.codRestrictEqLocusPushoutCocone.surjective_of_isEffective** 是 Mathlib 
中的一个定理，位于命名空间 `Algebra.codRestrictEqLocusPushoutCocone`。
形式化陈述：∀ (R S : Type u) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algeb
ra R S],   Algebra.IsEffective R S → Function.Surjective ⇑(Algebra.codRestrictEq
LocusPushoutCocone R S)
参数：R S : Type u；Algebra.codRestrictEqLocusPushoutCocone R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用引理 `Algebra.IsEffective.eqLocus_includeLeft_includeRight`：eqLocus_includeLef
t_includeRight (h : IsEffective R S) : TensorProduct.includeLeftRingHom.eqLocus 
TensorProduct.includeRight.toRingHom (S

--- 原说明 ---
`Algebra.IsEffective R S` implies surjectivity of `codRestrictEqLocusPushoutCoco
ne`.
-/
lemma codRestrictEqLocusPushoutCocone.surjective_of_isEffective (hf : Algebra.IsEffective R S) :
    Function.Surjective (codRestrictEqLocusPushoutCocone R S) := by
  intro ⟨s, hs⟩
  obtain ⟨t, rfl⟩ := Set.mem_range.mp <|
    Algebra.IsEffective.eqLocus_includeLeft_includeRight hf ▸ SetLike.mem_coe.mpr hs
  exact ⟨t, rfl⟩

/-- If `S` is a faithfully flat `R`-algebra, `codRestrictEqLocusPushoutCocone` is bijective. -/
/-
**Algebra.codRestrictEqLocusPushoutCocone.bijective_of_faithfullyFlat** 是 Mathli
b 中的一个定理，位于命名空间 `Algebra.codRestrictEqLocusPushoutCocone`。
形式化陈述：∀ (R S : Type u) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algeb
ra R S] [Module.FaithfullyFlat R S],   Function.Bijective ⇑(Algebra.codRestrictE
qLocusPushoutCocone R S)
参数：R S : Type u；Algebra.codRestrictEqLocusPushoutCocone R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.codRestrictEqLocusPushoutCocone.injective_of_faithfulSMul`：∀ (R 
S : Type u) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] [Fa
ithfulSMul R S],   Function.Injective ⇑(Algebra.codRest…
· 使用定理 `Algebra.codRestrictEqLocusPushoutCocone.surjective_of_isEffective`：∀ (R 
S : Type u) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S],   
Algebra.IsEffective R S → Function.Surjective ⇑(Algebra…
· 使用引理 `Algebra.IsEffective.of_faithfullyFlat`：of_faithfullyFlat [CommRing S] [A
lgebra R S] [Module.FaithfullyFlat R S] : IsEffective R S

--- 原说明 ---
If `S` is a faithfully flat `R`-algebra, `codRestrictEqLocusPushoutCocone` is bi
jective.
-/
lemma codRestrictEqLocusPushoutCocone.bijective_of_faithfullyFlat [Module.FaithfullyFlat R S] :
    Function.Bijective (codRestrictEqLocusPushoutCocone R S) := by
  constructor
  · exact codRestrictEqLocusPushoutCocone.injective_of_faithfulSMul _ _
  · exact codRestrictEqLocusPushoutCocone.surjective_of_isEffective _ _ (.of_faithfullyFlat R S)

end CodRestrictEqLocusPushoutCocone

end Algebra

