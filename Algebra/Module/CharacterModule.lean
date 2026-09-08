/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Junyan Xu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.Grp.Injective
public import Mathlib.Topology.Instances.AddCircle.Defs
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Character module of a module

For commutative ring `R` and an `R`-module `M` and an injective module `D`, its character module
`M⋆` is defined to be `R`-linear maps `M ⟶ D`.

`M⋆` also has an `R`-module structure given by `(r • f) m = f (r • m)`.

## Main results

- `CharacterModuleFunctor` : the contravariant functor of `R`-modules where `M ↦ M⋆` and
  an `R`-linear map `l : M ⟶ N` induces an `R`-linear map `l⋆ : f ↦ f ∘ l` where `f : N⋆`.
- `LinearMap.dual_surjective_of_injective` : If `l` is injective then `l⋆` is surjective,
  in another word taking character module as a functor sends monos to epis.
- `CharacterModule.homEquiv` : there is a bijection between linear map `Hom(N, M⋆)` and
  `(N ⊗ M)⋆` given by `curry` and `uncurry`.

-/

@[expose] public section

open CategoryTheory

universe uR uA uB

variable (R : Type uR) [CommRing R]
variable (A : Type uA) [AddCommGroup A]
variable (A' : Type*) [AddCommGroup A']
variable (B : Type uB) [AddCommGroup B]

/--
The character module of an abelian group `A` in the unit rational circle is `A⋆ := Hom_ℤ(A, ℚ ⧸ ℤ)`.
-/
/-
**CharacterModule** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：CharacterModule : Type uA
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The character module of an abelian group `A` in the unit rational circle is `A⋆ 
:= Hom_ℤ(A, ℚ ⧸ ℤ)`.
-/
def CharacterModule : Type uA := A →+ AddCircle (1 : ℚ)

namespace CharacterModule

set_option backward.isDefEq.respectTransparency.types false in
/-
**CharacterModule.** 是 Mathlib 中的一个实例，位于命名空间 `CharacterModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (CharacterModule A) A (AddCircle (1 : ℚ)) where
  coe c := c.toFun
  coe_injective _ _ _ := by simp_all
/-
**CharacterModule.** 是 Mathlib 中的一个实例，位于命名空间 `CharacterModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LinearMapClass (CharacterModule A) ℤ A (AddCircle (1 : ℚ)) where
  map_add := AddMonoidHom.map_add
  map_smulₛₗ := AddMonoidHom.map_zsmul
/-
**CharacterModule.** 是 Mathlib 中的一个实例，位于命名空间 `CharacterModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommGroup (CharacterModule A) :=
  inferInstanceAs (AddCommGroup (A →+ _))
/-
**CharacterModule.ext** 是 Mathlib 中的一个定理，位于命名空间 `CharacterModule`。
形式化陈述：∀ (A : Type uA) [inst : AddCommGroup A] {c c' : CharacterModule A}, (∀ (x 
: A), c x = c' x) → c = c'
参数：A : Type uA；∀ (x : A), c x = c' x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
@[ext] theorem ext {c c' : CharacterModule A} (h : ∀ x, c x = c' x) : c = c' := DFunLike.ext _ _ h

section module

variable [Module R A] [Module R A'] [Module R B]

set_option backward.isDefEq.respectTransparency false in
/-
**CharacterModule.** 是 Mathlib 中的一个实例，位于命名空间 `CharacterModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module R (CharacterModule A) :=
  fast_instance% Module.compHom (A →+ _) (RingEquiv.toOpposite _ |>.toRingHom : R →+* Rᵈᵐᵃ)

variable {R A B}
/-
**CharacterModule.smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `CharacterModule`。
形式化陈述：∀ {R : Type uR} [inst : CommRing R] {A : Type uA} [inst_1 : AddCommGroup A
] [inst_2 : _root_.Module R A]   (c : CharacterModule A) (r : R) (a : A), (r • c
) a = c (r • a)
参数：c : CharacterModule A；r : R；a : A；r • c；r • a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma smul_apply (c : CharacterModule A) (r : R) (a : A) : (r • c) a = c (r • a) := rfl

/--
Given an abelian group homomorphism `f : A → B`, `f⋆(L) := L ∘ f` defines a linear map
from `B⋆` to `A⋆`.
-/
/-
**CharacterModule.dual** 是 Mathlib 中的一个定义，位于命名空间 `CharacterModule`。
形式化陈述：{R : Type uR} →   [inst : CommRing R] →     {A : Type uA} →       [inst_1 
: AddCommGroup A] →         {B : Type uB} →           [inst_2 : AddCommGroup B] 
→             [inst_3 : _root_.Module R A] →               [inst_4 : _root_.Modu
le R B] → (A →ₗ[R] B) → CharacterModule B →ₗ[R] CharacterModule A
参数：A →ₗ[R] B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an abelian group homomorphism `f : A → B`, `f⋆(L) := L ∘ f` defines a line
ar map
from `B⋆` to `A⋆`.
-/
@[simps] def dual (f : A →ₗ[R] B) : CharacterModule B →ₗ[R] CharacterModule A where
  toFun L := L.comp f.toAddMonoidHom
  map_add' := by aesop
  map_smul' r c := by ext x; exact congr(c $(f.map_smul r x)).symm

@[simp]
/-
**CharacterModule.dual_zero** 是 Mathlib 中的一个引理，位于命名空间 `CharacterModule`。
形式化陈述：dual_zero : dual (0 : A ->ₗ[R] B) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `CharacterModule.ext`：∀ (A : Type uA) [inst : AddCommGroup A] {c c' : Cha
racterModule A}, (∀ (x : A), c x = c' x) → c = c'
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
· 使用定理 `CharacterModule.instLinearMapClassIntAddCircleRatOfNat`：∀ (A : Type uA) 
[inst : AddCommGroup A], LinearMapClass (CharacterModule A) ℤ A (AddCircle 1)
-/
lemma dual_zero : dual (0 : A →ₗ[R] B) = 0 := by
  ext f
  exact map_zero f
/-
**CharacterModule.dual_comp** 是 Mathlib 中的一个引理，位于命名空间 `CharacterModule`。
形式化陈述：dual_comp {C : Type*} [AddCommGroup C] [Module R C] (f : A ->ₗ[R] B) (g : 
B ->ₗ[R] C) : dual (g.comp f) = (dual f).comp (dual g)
参数：f : A ->ₗ[R] B；g : B ->ₗ[R] C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `CharacterModule.ext`：∀ (A : Type uA) [inst : AddCommGroup A] {c c' : Cha
racterModule A}, (∀ (x : A), c x = c' x) → c = c'
-/
lemma dual_comp {C : Type*} [AddCommGroup C] [Module R C] (f : A →ₗ[R] B) (g : B →ₗ[R] C) :
    dual (g.comp f) = (dual f).comp (dual g) := by
  ext
  rfl
/-
**CharacterModule.dual_injective_of_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Charac
terModule`。
形式化陈述：dual_injective_of_surjective (f : A ->ₗ[R] B) (hf : Function.Surjective f)
 : Function.Injective (dual f)
参数：f : A ->ₗ[R] B；hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CharacterModule.ext`：∀ (A : Type uA) [inst : AddCommGroup A] {c c' : Cha
racterModule A}, (∀ (x : A), c x = c' x) → c = c'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma dual_injective_of_surjective (f : A →ₗ[R] B) (hf : Function.Surjective f) :
    Function.Injective (dual f) := by
  intro φ ψ eq
  ext x
  obtain ⟨y, rfl⟩ := hf x
  change (dual f) φ _ = (dual f) ψ _
  rw [eq]
/-
**CharacterModule.dual_surjective_of_injective** 是 Mathlib 中的一个引理，位于命名空间 `Charac
terModule`。
形式化陈述：dual_surjective_of_injective (f : A ->ₗ[R] B) (hf : Function.Injective f) 
: Function.Surjective (dual f)
参数：f : A ->ₗ[R] B；hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Baer.extension_property_addMonoidHom`：extension_property_addMonoi
dHom (h : Module.Baer Int Q) (f : M ->+ N) (hf : Function.Injective f) (g : M ->
+ Q) : exists h : N ->+ Q, h.comp…
· 使用定理 `Module.Baer.of_divisible`：Module.Baer.of_divisible [DivisibleBy A Int] :
 Module.Baer Int A
-/
lemma dual_surjective_of_injective (f : A →ₗ[R] B) (hf : Function.Injective f) :
    Function.Surjective (dual f) :=
  (Module.Baer.of_divisible _).extension_property_addMonoidHom _ hf

/--
Two isomorphic modules have isomorphic character modules.
-/
/-
**CharacterModule.congr** 是 Mathlib 中的一个定义，位于命名空间 `CharacterModule`。
形式化陈述：congr (e : A ≃ₗ[R] B) : CharacterModule A ≃ₗ[R] CharacterModule B
参数：e : A ≃ₗ[R] B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two isomorphic modules have isomorphic character modules.
-/
def congr (e : A ≃ₗ[R] B) : CharacterModule A ≃ₗ[R] CharacterModule B :=
  .ofLinearMap (dual e.symm) (dual e)
    (by ext c _; exact congr(c $(e.right_inv _)))
    (by ext c _; exact congr(c $(e.left_inv _)))

open TensorProduct

set_option backward.isDefEq.respectTransparency.types false in
/--
Any linear map `L : A → B⋆` induces a character in `(A ⊗ B)⋆` by `a ⊗ b ↦ L a b`.
-/
/-
**CharacterModule.uncurry** 是 Mathlib 中的一个定义，位于命名空间 `CharacterModule`。
形式化陈述：{R : Type uR} →   [inst : CommRing R] →     {A : Type uA} →       [inst_1 
: AddCommGroup A] →         {B : Type uB} →           [inst_2 : AddCommGroup B] 
→             [inst_3 : _root_.Module R A] →               [inst_4 : _root_.Modu
le R B] → (A →ₗ[R] CharacterModule B) →ₗ[R] CharacterModule (TensorProduct R A B
)
参数：A →ₗ[R] CharacterModule B；TensorProduct R A B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any linear map `L : A → B⋆` induces a character in `(A ⊗ B)⋆` by `a ⊗ b ↦ L a b`
.
-/
@[simps] noncomputable def uncurry :
    (A →ₗ[R] CharacterModule B) →ₗ[R] CharacterModule (A ⊗[R] B) where
  toFun c := TensorProduct.liftAddHom c.toAddMonoidHom fun r a b ↦ congr($(c.map_smul r a) b)
  map_add' c c' := DFunLike.ext _ _ fun x ↦ by refine x.induction_on ?_ ?_ ?_ <;> aesop
  map_smul' r c := DFunLike.ext _ _ fun x ↦ x.induction_on
    (by simp_rw [map_zero]) (fun a b ↦ congr($(c.map_smul r a) b).symm) (by aesop)

/--
Any character `c` in `(A ⊗ B)⋆` induces a linear map `A → B⋆` by `a ↦ b ↦ c (a ⊗ b)`.
-/
/-
**CharacterModule.curry** 是 Mathlib 中的一个定义，位于命名空间 `CharacterModule`。
形式化陈述：{R : Type uR} →   [inst : CommRing R] →     {A : Type uA} →       [inst_1 
: AddCommGroup A] →         {B : Type uB} →           [inst_2 : AddCommGroup B] 
→             [inst_3 : _root_.Module R A] →               [inst_4 : _root_.Modu
le R B] → CharacterModule (TensorProduct R A B) →ₗ[R] A →ₗ[R] CharacterModule B
参数：TensorProduct R A B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any character `c` in `(A ⊗ B)⋆` induces a linear map `A → B⋆` by `a ↦ b ↦ c (a ⊗
 b)`.
-/
@[simps] noncomputable def curry :
    CharacterModule (A ⊗[R] B) →ₗ[R] (A →ₗ[R] CharacterModule B) where
  toFun c :=
  { toFun := (c.comp <| TensorProduct.mk R A B ·)
    map_add' := fun _ _ ↦ DFunLike.ext _ _ fun b ↦
      congr(c <| $(map_add (mk R A B) _ _) b).trans (c.map_add _ _)
    map_smul' := fun r a ↦ by ext; exact congr(c $(TensorProduct.tmul_smul _ _ _)).symm }
  map_add' _ _ := rfl
  map_smul' r c := by ext; exact congr(c $(TensorProduct.tmul_smul _ _ _)).symm

set_option backward.isDefEq.respectTransparency.types false in
/--
Linear maps into a character module are exactly characters of the tensor product.
-/
/-
**CharacterModule.homEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CharacterModule`。
形式化陈述：{R : Type uR} →   [inst : CommRing R] →     {A : Type uA} →       [inst_1 
: AddCommGroup A] →         {B : Type uB} →           [inst_2 : AddCommGroup B] 
→             [inst_3 : _root_.Module R A] →               [inst_4 : _root_.Modu
le R B] → (A →ₗ[R] CharacterModule B) ≃ₗ[R] CharacterModule (TensorProduct R A B
)
参数：A →ₗ[R] CharacterModule B；TensorProduct R A B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Linear maps into a character module are exactly characters of the tensor product
.
-/
@[simps!] noncomputable def homEquiv :
    (A →ₗ[R] CharacterModule B) ≃ₗ[R] CharacterModule (A ⊗[R] B) :=
  .ofLinearMap uncurry curry (by ext _ z; refine z.induction_on ?_ ?_ ?_ <;> aesop) (by aesop)
/-
**CharacterModule.dual_rTensor_conj_homEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Characte
rModule`。
形式化陈述：dual_rTensor_conj_homEquiv (f : A ->ₗ[R] A') : homEquiv.symm.toLinearMap ∘
ₗ dual (f.rTensor B) ∘ₗ homEquiv.toLinearMap = f.lcomp R _
参数：f : A ->ₗ[R] A'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dual_rTensor_conj_homEquiv (f : A →ₗ[R] A') :
    homEquiv.symm.toLinearMap ∘ₗ dual (f.rTensor B) ∘ₗ homEquiv.toLinearMap = f.lcomp R _ := rfl

end module

/--
`ℤ⋆`, the character module of `ℤ` in the unit rational circle.
-/
/-
**CharacterModule.int** 是 Mathlib 中的一个定义，位于命名空间 `CharacterModule`。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ℤ⋆`, the character module of `ℤ` in the unit rational circle.
-/
protected abbrev int : Type := CharacterModule ℤ

/-- Given `n : ℕ`, the map `m ↦ m / n`. -/
/-
**CharacterModule.int.divByNat** 是 Mathlib 中的一个定义，位于命名空间 `CharacterModule.int`。
形式化陈述：ℕ → CharacterModule.int
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `n : ℕ`, the map `m ↦ m / n`.
-/
protected abbrev int.divByNat (n : ℕ) : CharacterModule.int :=
  LinearMap.toSpanSingleton ℤ _ (QuotientAddGroup.mk (n : ℚ)⁻¹) |>.toAddMonoidHom
/-
**CharacterModule.int.divByNat_self** 是 Mathlib 中的一个定理，位于命名空间 `CharacterModule.i
nt`。
形式化陈述：∀ (n : ℕ), (CharacterModule.int.divByNat n) ↑n = 0
参数：n : ℕ；CharacterModule.int.divByNat n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
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
· 使用定理 `CharacterModule.instLinearMapClassIntAddCircleRatOfNat`：∀ (A : Type uA) 
[inst : AddCommGroup A], LinearMapClass (CharacterModule A) ℤ A (AddCircle 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AddCircle.coe_eq_zero_iff`：coe_eq_zero_iff {x : 𝕜} : (x : AddCircle p) =
 0 ↔ exists n : Int, n • p = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma int.divByNat_self (n : ℕ) :
    int.divByNat n n = 0 := by
  obtain rfl | h0 := eq_or_ne n 0
  · apply map_zero
  exact (AddCircle.coe_eq_zero_iff _).mpr
    ⟨1, by simp [mul_inv_cancel₀ (Nat.cast_ne_zero (R := ℚ).mpr h0)]⟩

variable {A}

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The `ℤ`-submodule spanned by a single element `a` is isomorphic to the quotient of `ℤ`
by the ideal generated by the order of `a`. -/
/-
**CharacterModule.intSpanEquivQuotAddOrderOf** 是 Mathlib 中的一个定义，位于命名空间 `Characte
rModule`。
形式化陈述：{A : Type uA} → [inst : AddCommGroup A] → (a : A) → ↥(ℤ ∙ a) ≃ₗ[ℤ] ℤ ⧸ Ide
al.span {↑(addOrderOf a)}
参数：a : A；ℤ ∙ a；addOrderOf a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `ℤ`-submodule spanned by a single element `a` is isomorphic to the quotient 
of `ℤ`
by the ideal generated by the order of `a`.
-/
@[simps!] noncomputable def intSpanEquivQuotAddOrderOf (a : A) :
    (ℤ ∙ a) ≃ₗ[ℤ] ℤ ⧸ Ideal.span {(addOrderOf a : ℤ)} :=
  LinearEquiv.ofEq _ _ (LinearMap.span_singleton_eq_range ℤ A a) ≪≫ₗ
  (LinearMap.quotKerEquivRange <| LinearMap.toSpanSingleton ℤ A a).symm ≪≫ₗ
  Submodule.quotEquivOfEq _ _ (by
    ext1 x
    rw [Ideal.mem_span_singleton, addOrderOf_dvd_iff_zsmul_eq_zero, LinearMap.mem_ker,
      LinearMap.toSpanSingleton_apply])
/-
**CharacterModule.intSpanEquivQuotAddOrderOf_apply_self** 是 Mathlib 中的一个引理，位于命名空
间 `CharacterModule`。
形式化陈述：intSpanEquivQuotAddOrderOf_apply_self (a : A) : intSpanEquivQuotAddOrderOf
 a ⟨a, Submodule.mem_span_singleton_self a⟩ = Submodule.Quotient.mk 1
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_span_singleton_self`：mem_span_singleton_self (x : M) : x i
n R ∙ x
· 使用定理 `LinearEquiv.eq_symm_apply`：eq_symm_apply {x y} : y = e.symm x ↔ e y = x
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 1 • a = a
-/
lemma intSpanEquivQuotAddOrderOf_apply_self (a : A) :
    intSpanEquivQuotAddOrderOf a ⟨a, Submodule.mem_span_singleton_self a⟩ =
    Submodule.Quotient.mk 1 :=
  (LinearEquiv.eq_symm_apply _).mp <| Subtype.ext (one_zsmul _).symm

/--
For an abelian group `A` and an element `a ∈ A`, there is a character `c : ℤ ∙ a → ℚ ⧸ ℤ` given by
`m • a ↦ m / n` where `n` is the smallest positive integer such that `n • a = 0` and when such `n`
does not exist, `c` is defined by `m • a ↦ m / 2`.
-/
/-
**CharacterModule.ofSpanSingleton** 是 Mathlib 中的一个定义，位于命名空间 `CharacterModule`。
形式化陈述：ofSpanSingleton (a : A) : CharacterModule (Int ∙ a)
参数：a : A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For an abelian group `A` and an element `a ∈ A`, there is a character `c : ℤ ∙ a
 → ℚ ⧸ ℤ` given by
`m • a ↦ m / n` where `n` is the smallest positive integer such that `n • a = 0`
 and when such `n`
does not exist, `c` is defined by `m • a ↦ m / 2`.
-/
noncomputable def ofSpanSingleton (a : A) : CharacterModule (ℤ ∙ a) :=
  let l : ℤ ⧸ Ideal.span {(addOrderOf a : ℤ)} →ₗ[ℤ] AddCircle (1 : ℚ) :=
    Submodule.liftQSpanSingleton _
      (CharacterModule.int.divByNat <|
        if addOrderOf a = 0 then 2 else addOrderOf a).toIntLinearMap <| by
        split_ifs with h
        · rw [h, Nat.cast_zero, map_zero]
        · apply CharacterModule.int.divByNat_self
  l ∘ₗ intSpanEquivQuotAddOrderOf a |>.toAddMonoidHom
/-
**CharacterModule.eq_zero_of_ofSpanSingleton_apply_self** 是 Mathlib 中的一个引理，位于命名空
间 `CharacterModule`。
形式化陈述：eq_zero_of_ofSpanSingleton_apply_self (a : A) (h : ofSpanSingleton a ⟨a, S
ubmodule.mem_span_singleton_self a⟩ = 0) : a = 0
参数：a : A；h : ofSpanSingleton a ⟨a, Submodule.mem_span_singleton_self a⟩ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.mem_span_singleton_self`：mem_span_singleton_self (x : M) : x i
n R ∙ x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddCircle.coe_eq_zero_iff`：coe_eq_zero_iff {x : 𝕜} : (x : AddCircle p) =
 0 ↔ exists n : Int, n • p = x
· 使用定理 `LinearMap.toSpanSingleton_apply_one`：toSpanSingleton_apply_one (x : M) :
 toSpanSingleton R M x 1 = x
· 使用定理 `CharacterModule.int.divByNat.eq_1`：∀ (n : ℕ),   CharacterModule.int.divB
yNat n = (LinearMap.toSpanSingleton ℤ (ℚ ⧸ AddSubgroup.zmultiples 1) ↑(↑n)⁻¹).to
AddMonoidHom
· 使用定理 `AddMonoidHom.coe_toIntLinearMap`：AddMonoidHom.coe_toIntLinearMap [AddCom
mGroup M] [AddCommGroup M₂] (f : M ->+ M₂) : ⇑f.toIntLinearMap = f
· 使用定理 `Submodule.liftQSpanSingleton_apply`：liftQSpanSingleton_apply (x : M) (f 
: M ->ₛₗ[τ₁₂] M₂) (h : f x = 0) (y : M) : liftQSpanSingleton x f h (Quotient.mk 
y) = f y
· 使用引理 `CharacterModule.intSpanEquivQuotAddOrderOf_apply_self`：intSpanEquivQuotA
ddOrderOf_apply_self (a : A) : intSpanEquivQuotAddOrderOf a ⟨a, Submodule.mem_sp
an_singleton_self a⟩ = Submodule.Quotient.m…
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
· 使用引理 `LinearMap.toAddMonoidHom_coe`：toAddMonoidHom_coe {modM₁ : Module R M₁} {
modM₂ : Module S M₂} {σ : R ->+* S} (f : M₁ ->ₛₗ[σ] M₂) : ⇑f.toAddMonoidHom = f
· 使用定理 `CharacterModule.ofSpanSingleton.eq_1`：∀ {A : Type uA} [inst : AddCommGro
up A] (a : A),   CharacterModule.ofSpanSingleton a =     (Submodule.liftQSpanSin
gleton (↑(addOrderOf a))  …
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Rat.inv_natCast_den_of_pos`：inv_natCast_den_of_pos {a : Nat} (ha0 : 0 < 
a) : (a : Rat)⁻¹.den = a
· 使用定理 `Rat.den_intCast`：∀ (a : ℤ), (↑a).den = 1
· 使用定理 `zsmul_one`：∀ {R : Type u_1} [inst : AddGroupWithOne R] (n : ℤ), n • 1 = 
↑n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `AddMonoid.addOrderOf_eq_one_iff`：∀ {G : Type u_1} [inst : AddMonoid G] {
x : G}, addOrderOf x = 1 ↔ x = 0
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
lemma eq_zero_of_ofSpanSingleton_apply_self (a : A)
    (h : ofSpanSingleton a ⟨a, Submodule.mem_span_singleton_self a⟩ = 0) : a = 0 := by
  erw [ofSpanSingleton, LinearMap.toAddMonoidHom_coe, LinearMap.comp_apply,
     intSpanEquivQuotAddOrderOf_apply_self, Submodule.liftQSpanSingleton_apply,
    AddMonoidHom.coe_toIntLinearMap, int.divByNat, LinearMap.toSpanSingleton_apply_one,
    AddCircle.coe_eq_zero_iff] at h
  rcases h with ⟨n, hn⟩
  apply_fun Rat.den at hn
  rw [zsmul_one, Rat.den_intCast, Rat.inv_natCast_den_of_pos] at hn
  · split_ifs at hn
    · cases hn
    · rwa [eq_comm, AddMonoid.addOrderOf_eq_one_iff] at hn
  · grind
/-
**CharacterModule.exists_character_apply_ne_zero_of_ne_zero** 是 Mathlib 中的一个引理，位
于命名空间 `CharacterModule`。
形式化陈述：exists_character_apply_ne_zero_of_ne_zero {a : A} (ne_zero : a != 0) : exi
sts (c : CharacterModule A), c a != 0
参数：ne_zero : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CharacterModule.dual_surjective_of_injective`：dual_surjective_of_injecti
ve (f : A ->ₗ[R] B) (hf : Function.Injective f) : Function.Surjective (dual f)
· 使用定理 `Submodule.injective_subtype`：injective_subtype : Injective p.subtype
· 使用引理 `CharacterModule.eq_zero_of_ofSpanSingleton_apply_self`：eq_zero_of_ofSpan
Singleton_apply_self (a : A) (h : ofSpanSingleton a ⟨a, Submodule.mem_span_singl
eton_self a⟩ = 0) : a = 0
· 使用定理 `Submodule.mem_span_singleton_self`：mem_span_singleton_self (x : M) : x i
n R ∙ x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma exists_character_apply_ne_zero_of_ne_zero {a : A} (ne_zero : a ≠ 0) :
    ∃ (c : CharacterModule A), c a ≠ 0 :=
  have ⟨c, hc⟩ := dual_surjective_of_injective _ (Submodule.injective_subtype _) (ofSpanSingleton a)
  ⟨c, fun h ↦ ne_zero <| eq_zero_of_ofSpanSingleton_apply_self a <| by rwa [← hc]⟩
/-
**CharacterModule.eq_zero_of_character_apply** 是 Mathlib 中的一个引理，位于命名空间 `Characte
rModule`。
形式化陈述：eq_zero_of_character_apply {a : A} (h : forall c : CharacterModule A, c a 
= 0) : a = 0
参数：h : forall c : CharacterModule A, c a = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用引理 `CharacterModule.exists_character_apply_ne_zero_of_ne_zero`：exists_charac
ter_apply_ne_zero_of_ne_zero {a : A} (ne_zero : a != 0) : exists (c : CharacterM
odule A), c a != 0
-/
lemma eq_zero_of_character_apply {a : A} (h : ∀ c : CharacterModule A, c a = 0) : a = 0 := by
  contrapose! h; exact exists_character_apply_ne_zero_of_ne_zero h

variable [Module R A] [Module R A'] [Module R B] {R A' B}
/-
**CharacterModule.dual_surjective_iff_injective** 是 Mathlib 中的一个引理，位于命名空间 `Chara
cterModule`。
形式化陈述：dual_surjective_iff_injective {f : A ->ₗ[R] A'} : Function.Surjective (dua
l f) ↔ Function.Injective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `injective_iff_map_eq_zero`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9
} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [AddM
onoidHomClass F…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用引理 `CharacterModule.eq_zero_of_character_apply`：eq_zero_of_character_apply {
a : A} (h : forall c : CharacterModule A, c a = 0) : a = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidHom.map_zero`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M
] [inst_1 : AddZero N] (f : M →+ N), f 0 = 0
· 使用引理 `CharacterModule.dual_surjective_of_injective`：dual_surjective_of_injecti
ve (f : A ->ₗ[R] B) (hf : Function.Injective f) : Function.Surjective (dual f)
-/
lemma dual_surjective_iff_injective {f : A →ₗ[R] A'} :
    Function.Surjective (dual f) ↔ Function.Injective f :=
  ⟨fun h ↦ (injective_iff_map_eq_zero _).2 fun a h0 ↦ eq_zero_of_character_apply fun c ↦ by
    obtain ⟨c, rfl⟩ := h c; exact congr(c $h0).trans c.map_zero,
  dual_surjective_of_injective f⟩
/-
**CharacterModule._root_.rTensor_injective_iff_lcomp_surjective** 是 Mathlib 中的一个
定理，位于命名空间 `CharacterModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.rTensor_injective_iff_lcomp_surjective {f : A →ₗ[R] A'} :
    Function.Injective (f.rTensor B) ↔ Function.Surjective (f.lcomp R <| CharacterModule B) := by
  simp [← dual_rTensor_conj_homEquiv, dual_surjective_iff_injective]

set_option backward.isDefEq.respectTransparency false in
/-
**CharacterModule.surjective_of_dual_injective** 是 Mathlib 中的一个引理，位于命名空间 `Charac
terModule`。
形式化陈述：surjective_of_dual_injective (f : A ->ₗ[R] A') (hf : Function.Injective (d
ual f)) : Function.Surjective f
参数：f : A ->ₗ[R] A'；hf : Function.Injective (dual f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `Submodule.unique_quotient_iff_eq_top`：unique_quotient_iff_eq_top : Nonem
pty (Unique (M ⧸ p)) ↔ p = ⊤
· 使用引理 `CharacterModule.eq_zero_of_character_apply`：eq_zero_of_character_apply {
a : A} (h : forall c : CharacterModule A, c a = 0) : a = 0
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `QuotientAddGroup.mk'_surjective`：∀ {G : Type u_1} [inst : AddGroup G] (N
 : AddSubgroup G) [nN : N.Normal], Function.Surjective ⇑(QuotientAddGroup.mk' N)
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
· 使用引理 `CharacterModule.dual_comp`：dual_comp {C : Type*} [AddCommGroup C] [Modul
e R C] (f : A ->ₗ[R] B) (g : B ->ₗ[R] C) : dual (g.comp f) = (dual f).comp (dual
 g)
· 使用定理 `LinearMap.range_mkQ_comp`：range_mkQ_comp (f : M ->ₛₗ[τ₁₂] M₂) : (range f
).mkQ.comp f = 0
· 使用引理 `CharacterModule.dual_zero`：dual_zero : dual (0 : A ->ₗ[R] B) = 0
· 使用定理 `LinearMap.zero_apply`：zero_apply (x : M) : (0 : M ->ₛₗ[σ₁₂] M₂) x = 0
· 使用定理 `CharacterModule.dual_apply`：∀ {R : Type uR} [inst : CommRing R] {A : Typ
e uA} [inst_1 : AddCommGroup A] {B : Type uB} [inst_2 : AddCommGroup B]   [inst_
3 : _root_.Modul…
· 使用定理 `AddMonoidHom.zero_comp`：∀ {M : Type u_4} {N : Type u_5} {P : Type u_6} [
inst : AddZero M] [inst_1 : AddZero N] [inst_2 : AddZeroClass P]   (f : M →+ N),
 AddMonoidHo…
-/
lemma surjective_of_dual_injective (f : A →ₗ[R] A') (hf : Function.Injective (dual f)) :
    Function.Surjective f := by
  rw [← LinearMap.range_eq_top, ← Submodule.unique_quotient_iff_eq_top]
  refine ⟨Unique.mk inferInstance fun a ↦ eq_zero_of_character_apply fun c ↦ ?_⟩
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk'_surjective _ a
  suffices eq : dual (Submodule.mkQ _) c = 0 from congr($eq b)
  refine hf ?_
  rw [← LinearMap.comp_apply, ← dual_comp, LinearMap.range_mkQ_comp, dual_zero,
    LinearMap.zero_apply, dual_apply, AddMonoidHom.zero_comp]
/-
**CharacterModule.dual_injective_iff_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Chara
cterModule`。
形式化陈述：dual_injective_iff_surjective {f : A ->ₗ[R] A'} : Function.Injective (dual
 f) ↔ Function.Surjective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CharacterModule.surjective_of_dual_injective`：surjective_of_dual_injecti
ve (f : A ->ₗ[R] A') (hf : Function.Injective (dual f)) : Function.Surjective f
· 使用引理 `CharacterModule.dual_injective_of_surjective`：dual_injective_of_surjecti
ve (f : A ->ₗ[R] B) (hf : Function.Surjective f) : Function.Injective (dual f)
-/
lemma dual_injective_iff_surjective {f : A →ₗ[R] A'} :
    Function.Injective (dual f) ↔ Function.Surjective f :=
  ⟨fun h ↦ surjective_of_dual_injective f h, fun h ↦ dual_injective_of_surjective f h⟩
/-
**CharacterModule.dual_bijective_iff_bijective** 是 Mathlib 中的一个引理，位于命名空间 `Charac
terModule`。
形式化陈述：dual_bijective_iff_bijective {f : A ->ₗ[R] A'} : Function.Bijective (dual 
f) ↔ Function.Bijective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `CharacterModule.dual_surjective_iff_injective`：dual_surjective_iff_injec
tive {f : A ->ₗ[R] A'} : Function.Surjective (dual f) ↔ Function.Injective f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `CharacterModule.dual_injective_iff_surjective`：dual_injective_iff_surjec
tive {f : A ->ₗ[R] A'} : Function.Injective (dual f) ↔ Function.Surjective f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
lemma dual_bijective_iff_bijective {f : A →ₗ[R] A'} :
    Function.Bijective (dual f) ↔ Function.Bijective f :=
  ⟨fun h ↦ ⟨dual_surjective_iff_injective.mp h.2, dual_injective_iff_surjective.mp h.1⟩,
  fun h ↦ ⟨dual_injective_iff_surjective.mpr h.2, dual_surjective_iff_injective.mpr h.1⟩⟩

end CharacterModule

