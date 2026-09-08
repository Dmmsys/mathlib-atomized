/-
Copyright (c) 2025 Stepan Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stepan Nesterov, Edison Xie
-/
module

public import Mathlib.RepresentationTheory.Subrepresentation

/-!
# Intertwining maps

This file gives defines intertwining maps of representations (aka equivariant linear maps).

-/

@[expose] public section

open scoped MonoidAlgebra

namespace Representation

section non_comm
section Monoid

variable {A G V W U : Type*} [Semiring A] [Monoid G] [AddCommMonoid V] [AddCommMonoid W]
  [AddCommMonoid U] [Module A V] [Module A W] [Module A U] (ρ : Representation A G V)
  (σ : Representation A G W) (τ : Representation A G U) (f : V →ₗ[A] W)

/-- An unbundled version of `IntertwiningMap`. -/
/-
**Representation.IsIntertwiningMap** 是 Mathlib 中的一个归纳类型，位于命名空间 `Representation`。
形式化陈述：{A : Type u_1} →   {G : Type u_2} →     {V : Type u_3} →       {W : Type u
_4} →         [inst : Semiring A] →           [inst_1 : Monoid G] →             
[inst_2 : AddCommMonoid V] →               [inst_3 : AddCommMonoid W] →         
        [inst_4 : _root_.Module A V] →                   [inst_5 : _root_.Module
 A W] → Representation A G V → Representation A G W → (V →ₗ[A] W) → Prop
参数：V →ₗ[A] W。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An unbundled version of `IntertwiningMap`.
-/
@[mk_iff] structure IsIntertwiningMap : Prop where
  isIntertwining (g : G) (v : V) : f (ρ g v) = σ g (f v)

/-- An intertwining map between two representations `ρ` and `σ` of the same monoid `G` is a map
  between underlying modules which commutes with the `G`-actions. -/
/-
**Representation.IntertwiningMap** 是 Mathlib 中的一个归纳类型，位于命名空间 `Representation`。
形式化陈述：{A : Type u_1} →   {G : Type u_2} →     {V : Type u_3} →       {W : Type u
_4} →         [inst : Semiring A] →           [inst_1 : Monoid G] →             
[inst_2 : AddCommMonoid V] →               [inst_3 : AddCommMonoid W] →         
        [inst_4 : _root_.Module A V] →                   [inst_5 : _root_.Module
 A W] → Representation A G V → Representation A G W → Type (max u_3 u_4)
参数：max u_3 u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An intertwining map between two representations `ρ` and `σ` of the same monoid `
G` is a map
  between underlying modules which commutes with the `G`-actions.
-/
structure IntertwiningMap extends V →ₗ[A] W where
  /-- An underlying `A`-linear map of the underlying `A`-modules. -/
  isIntertwining' (g : G) : toLinearMap ∘ₗ ρ g = σ g ∘ₗ toLinearMap

/-- An intertwining map constructed form the linear map and the fact that it is intertwining. -/
/-
**Representation._root_.LinearMap.intertwiningMap_of_isIntertwiningMap** 是 Mathl
ib 中的一个定义，位于命名空间 `Representation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An intertwining map constructed form the linear map and the fact that it is inte
rtwining.
-/
def _root_.LinearMap.intertwiningMap_of_isIntertwiningMap
    (hf : ∀ (g : G), ∀ (v : V), f (ρ g v) = σ g (f v)) : IntertwiningMap ρ σ :=
  { f with isIntertwining' g := by ext v; exact hf g v }
/-
**Representation.IntertwiningMap.isIntertwining_assoc** 是 Mathlib 中的一个定理，位于命名空间 
`Representation.IntertwiningMap`。
形式化陈述：∀ {A : Type u_1} {G : Type u_2} {V : Type u_3} {W : Type u_4} {U : Type u_
5} [inst : Semiring A] [inst_1 : Monoid G]   [inst_2 : AddCommMonoid V] [inst_3 
: AddCommMonoid W] [inst_4 : AddCommMonoid U] [inst_5 : _root_.Module A V]   [in
st_6 : _root_.Module A W] [inst_7 : _root_.Module A U] (ρ : Representation A G V
) (σ : Representation A G W)   {f : ρ.IntertwiningMap σ} (g : G) (l : U →ₗ[A] V)
, f.toLinearMap ∘ₗ ρ g ∘ₗ l = σ g ∘ₗ f.toLinearMap ∘ₗ l
参数：ρ : Representation A G V；σ : Representation A G W；g : G；l : U →ₗ[A] V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.comp_assoc`：comp_assoc {R₄ M₄ : Type*} [Semiring R₄] [AddCommM
onoid M₄] [Module R₄ M₄] {σ₃₄ : R₃ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₁₄ : R₁ ->+* R₄
} [RingHom…
· 使用定理 `Representation.IntertwiningMap.isIntertwining'`：∀ {A : Type u_1} {G : Ty
pe u_2} {V : Type u_3} {W : Type u_4} [inst : Semiring A] [inst_1 : Monoid G]   
[inst_2 : AddCommMonoid V] [inst_3 :…
-/
lemma IntertwiningMap.isIntertwining_assoc {f : IntertwiningMap ρ σ} (g : G) (l : U →ₗ[A] V) :
    f.toLinearMap ∘ₗ ρ g ∘ₗ l = σ g ∘ₗ f.toLinearMap ∘ₗ l := by
  rw [← LinearMap.comp_assoc, f.2, LinearMap.comp_assoc]

namespace IntertwiningMap

variable {ρ σ} in
@[ext]
/-
**Representation.IntertwiningMap.ext** 是 Mathlib 中的一个引理，位于命名空间 `Representation.I
ntertwiningMap`。
形式化陈述：ext {f g : IntertwiningMap ρ σ} (h : f.toLinearMap = g.toLinearMap) : f = 
g
参数：h : f.toLinearMap = g.toLinearMap。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Representation.IntertwiningMap.mk.injEq`：∀ {A : Type u_1} {G : Type u_2}
 {V : Type u_3} {W : Type u_4} [inst : Semiring A] [inst_1 : Monoid G]   [inst_2
 : AddCommMonoid V] [inst_3 :…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma ext {f g : IntertwiningMap ρ σ} (h : f.toLinearMap = g.toLinearMap) : f = g := by
  cases f; cases g
  simpa using h
/-
**Representation.IntertwiningMap.toLinearMap_injective** 是 Mathlib 中的一个引理，位于命名空间
 `Representation.IntertwiningMap`。
形式化陈述：toLinearMap_injective : Function.Injective fun f : IntertwiningMap ρ σ => 
f.toLinearMap
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Representation.IntertwiningMap.ext`：ext {f g : IntertwiningMap ρ σ} (h :
 f.toLinearMap = g.toLinearMap) : f = g
-/
lemma toLinearMap_injective : Function.Injective fun f : IntertwiningMap ρ σ ↦ f.toLinearMap :=
  fun _ _ ↦ ext
/-
**Representation.IntertwiningMap.toFun_injective** 是 Mathlib 中的一个引理，位于命名空间 `Repr
esentation.IntertwiningMap`。
形式化陈述：toFun_injective : Function.Injective fun f : IntertwiningMap ρ σ => f.toLi
nearMap.toFun
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Representation.IntertwiningMap.ext`：ext {f g : IntertwiningMap ρ σ} (h :
 f.toLinearMap = g.toLinearMap) : f = g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
-/
lemma toFun_injective : Function.Injective fun f : IntertwiningMap ρ σ ↦ f.toLinearMap.toFun := by
  intro f g h
  ext x
  exact congrFun h x
/-
**Representation.IntertwiningMap.** 是 Mathlib 中的一个实例，位于命名空间 `Representation.Inte
rtwiningMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (IntertwiningMap ρ σ) V W where
  coe f := f.toFun
  coe_injective := toFun_injective ρ σ
/-
**Representation.IntertwiningMap.** 是 Mathlib 中的一个实例，位于命名空间 `Representation.Inte
rtwiningMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LinearMapClass (IntertwiningMap ρ σ) A V W where
  map_add f := f.map_add
  map_smulₛₗ f := f.map_smul

-- Despite the other bundled homs having the inverse direction as simp lemmas,
-- we are actively moving away from these design decisions.
-- See e.g. https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Concrete.20homomorphism.20type.20vs.20abstract.20class/with/492579416
@[simp]
/-
**Representation.IntertwiningMap.coe_eq_toLinearMap** 是 Mathlib 中的一个引理，位于命名空间 `R
epresentation.IntertwiningMap`。
形式化陈述：coe_eq_toLinearMap {f : IntertwiningMap ρ σ} : SemilinearMapClass.semiline
arMap f = f.toLinearMap
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Representation.IntertwiningMap.instLinearMapClass`：∀ {A : Type u_1} {G :
 Type u_2} {V : Type u_3} {W : Type u_4} [inst : Semiring A] [inst_1 : Monoid G]
   [inst_2 : AddCommMonoid V] [inst_3 :…
-/
lemma coe_eq_toLinearMap {f : IntertwiningMap ρ σ} :
  SemilinearMapClass.semilinearMap f = f.toLinearMap := rfl
/-
**Representation.IntertwiningMap.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `Representatio
n.IntertwiningMap`。
形式化陈述：∀ {A : Type u_1} {G : Type u_2} {V : Type u_3} {W : Type u_4} [inst : Semi
ring A] [inst_1 : Monoid G]   [inst_2 : AddCommMonoid V] [inst_3 : AddCommMonoid
 W] [inst_4 : _root_.Module A V] [inst_5 : _root_.Module A W]   (ρ : Representat
ion A G V) (σ : Representation A G W) (f : V →ₗ[A] W) (h : ∀ (g : G), f ∘ₗ ρ g =
 σ g ∘ₗ f),   ⇑{ toLinearMap := f, isIntertwining' := h } = ⇑f
参数：ρ : Representation A G V；σ : Representation A G W；f : V →ₗ[A] W；h : ∀ (g : G)
, f ∘ₗ ρ g = σ g ∘ₗ f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_mk (f : V →ₗ[A] W) (h) : ⇑(⟨f, h⟩ : IntertwiningMap ρ σ) = f := rfl
/-
**Representation.IntertwiningMap.toLinearMap_mk** 是 Mathlib 中的一个引理，位于命名空间 `Repre
sentation.IntertwiningMap`。
形式化陈述：toLinearMap_mk (f : V ->ₗ[A] W) (h) : (⟨f, h⟩ : IntertwiningMap ρ σ).toLin
earMap = f
参数：f : V ->ₗ[A] W；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toLinearMap_mk (f : V →ₗ[A] W) (h) :
  (⟨f, h⟩ : IntertwiningMap ρ σ).toLinearMap = f := rfl
/-
**Representation.IntertwiningMap.isIntertwining** 是 Mathlib 中的一个引理，位于命名空间 `Repre
sentation.IntertwiningMap`。
形式化陈述：isIntertwining (f : IntertwiningMap ρ σ) (g : G) (v : V) : f (ρ g v) = σ g
 (f v)
参数：f : IntertwiningMap ρ σ；g : G；v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Representation.IntertwiningMap.isIntertwining'`：∀ {A : Type u_1} {G : Ty
pe u_2} {V : Type u_3} {W : Type u_4} [inst : Semiring A] [inst_1 : Monoid G]   
[inst_2 : AddCommMonoid V] [inst_3 :…
-/
lemma isIntertwining (f : IntertwiningMap ρ σ) (g : G) (v : V) :
    f (ρ g v) = σ g (f v) := congr($(f.isIntertwining' g) v)
/-
**Representation.IntertwiningMap.toLinearMap_apply** 是 Mathlib 中的一个引理，位于命名空间 `Re
presentation.IntertwiningMap`。
形式化陈述：toLinearMap_apply (f : IntertwiningMap ρ σ) (v : V) : f.toLinearMap v = f 
v
参数：f : IntertwiningMap ρ σ；v : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toLinearMap_apply (f : IntertwiningMap ρ σ) (v : V) : f.toLinearMap v = f v := rfl
/-
**Representation.IntertwiningMap.coe_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `Repr
esentation.IntertwiningMap`。
形式化陈述：∀ {A : Type u_1} {G : Type u_2} {V : Type u_3} {W : Type u_4} [inst : Semi
ring A] [inst_1 : Monoid G]   [inst_2 : AddCommMonoid V] [inst_3 : AddCommMonoid
 W] [inst_4 : _root_.Module A V] [inst_5 : _root_.Module A W]   (ρ : Representat
ion A G V) (σ : Representation A G W) (f : ρ.IntertwiningMap σ), ⇑f.toLinearMap 
= ⇑f
参数：ρ : Representation A G V；σ : Representation A G W；f : ρ.IntertwiningMap σ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_toLinearMap (f : IntertwiningMap ρ σ) : (f.toLinearMap : _ → _) = f := rfl
/-
**Representation.IntertwiningMap._root_.LinearMap.toIntertwiningMap** 是 Mathlib 
中的一个引理，位于命名空间 `Representation.IntertwiningMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.LinearMap.toIntertwiningMap
  (hf : ∀ (g : G), ∀ (v : V), f (ρ g v) = σ g (f v)) (v : V) :
  f.intertwiningMap_of_isIntertwiningMap ρ σ hf v = f v := rfl
/-
**Representation.IntertwiningMap.** 是 Mathlib 中的一个实例，位于命名空间 `Representation.Inte
rtwiningMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (IntertwiningMap ρ σ) := ⟨⟨0, by simp⟩⟩
/-
**Representation.IntertwiningMap.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `Representat
ion.IntertwiningMap`。
形式化陈述：∀ {A : Type u_1} {G : Type u_2} {V : Type u_3} {W : Type u_4} [inst : Semi
ring A] [inst_1 : Monoid G]   [inst_2 : AddCommMonoid V] [inst_3 : AddCommMonoid
 W] [inst_4 : _root_.Module A V] [inst_5 : _root_.Module A W]   (ρ : Representat
ion A G V) (σ : Representation A G W), ⇑0 = 0
参数：ρ : Representation A G V；σ : Representation A G W。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_zero : ((0 : IntertwiningMap ρ σ) : V → W) = 0 := rfl
/-
**Representation.IntertwiningMap.zero_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `Rep
resentation.IntertwiningMap`。
形式化陈述：∀ {A : Type u_1} {G : Type u_2} {V : Type u_3} {W : Type u_4} [inst : Semi
ring A] [inst_1 : Monoid G]   [inst_2 : AddCommMonoid V] [inst_3 : AddCommMonoid
 W] [inst_4 : _root_.Module A V] [inst_5 : _root_.Module A W]   (ρ : Representat
ion A G V) (σ : Representation A G W), Representation.IntertwiningMap.toLinearMa
p 0 = 0
参数：ρ : Representation A G V；σ : Representation A G W。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma zero_toLinearMap : (0 : IntertwiningMap ρ σ).toLinearMap = 0 := rfl
/-
**Representation.IntertwiningMap.** 是 Mathlib 中的一个实例，位于命名空间 `Representation.Inte
rtwiningMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add (IntertwiningMap ρ σ) :=
  ⟨fun f g ↦ ⟨f.toLinearMap + g.toLinearMap, by
    simp [LinearMap.add_comp, LinearMap.comp_add, f.2, g.2,]⟩⟩
/-
**Representation.IntertwiningMap.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `Representati
on.IntertwiningMap`。
形式化陈述：∀ {A : Type u_1} {G : Type u_2} {V : Type u_3} {W : Type u_4} [inst : Semi
ring A] [inst_1 : Monoid G]   [inst_2 : AddCommMonoid V] [inst_3 : AddCommMonoid
 W] [inst_4 : _root_.Module A V] [inst_5 : _root_.Module A W]   (ρ : Representat
ion A G V) (σ : Representation A G W) (f g : ρ.IntertwiningMap σ), ⇑(f + g) = ⇑f
 + ⇑g
参数：ρ : Representation A G V；σ : Representation A G W；f g : ρ.IntertwiningMap σ；f
 + g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_add (f g : IntertwiningMap ρ σ) :
    ((f + g : IntertwiningMap ρ σ) : V → W) = f + g := rfl

@[simp]
/-
**Representation.IntertwiningMap.add_toLinearMap** 是 Mathlib 中的一个引理，位于命名空间 `Repr
esentation.IntertwiningMap`。
形式化陈述：add_toLinearMap (f g : IntertwiningMap ρ σ) : (f + g).toLinearMap = f.toLi
nearMap + g.toLinearMap
参数：f g : IntertwiningMap ρ σ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma add_toLinearMap (f g : IntertwiningMap ρ σ) :
    (f + g).toLinearMap = f.toLinearMap + g.toLinearMap := rfl
/-
**Representation.IntertwiningMap.** 是 Mathlib 中的一个实例，位于命名空间 `Representation.Inte
rtwiningMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul ℕ (IntertwiningMap ρ σ) :=
  ⟨fun n f ↦ ⟨n • f.toLinearMap, by simp [LinearMap.smul_comp, LinearMap.comp_smul, f.2]⟩⟩
/-
**Representation.IntertwiningMap.coe_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `Representa
tion.IntertwiningMap`。
形式化陈述：∀ {A : Type u_1} {G : Type u_2} {V : Type u_3} {W : Type u_4} [inst : Semi
ring A] [inst_1 : Monoid G]   [inst_2 : AddCommMonoid V] [inst_3 : AddCommMonoid
 W] [inst_4 : _root_.Module A V] [inst_5 : _root_.Module A W]   (ρ : Representat
ion A G V) (σ : Representation A G W) (f : ρ.IntertwiningMap σ) (n : ℕ), ⇑(n • f
) = n • ⇑f
参数：ρ : Representation A G V；σ : Representation A G W；f : ρ.IntertwiningMap σ；n :
 ℕ；n • f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_nsmul (f : IntertwiningMap ρ σ) (n : ℕ) :
    ((n • f : IntertwiningMap ρ σ) : V → W) = n • f := rfl
/-
**Representation.IntertwiningMap.instAddCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Re
presentation.IntertwiningMap`。
形式化陈述：instAddCommMonoid : AddCommMonoid (IntertwiningMap ρ σ)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommMonoid : AddCommMonoid (IntertwiningMap ρ σ) :=
  fast_instance%
  DFunLike.coe_injective.addCommMonoid _ (coe_zero ρ σ) (coe_add ρ σ) (by intro f n; rw [coe_nsmul])

/-- The range of an intertwining map from `V` to `W` as a subrepresentation of `W`. -/
@[simps]
/-
**Representation.IntertwiningMap.range** 是 Mathlib 中的一个定义，位于命名空间 `Representation
.IntertwiningMap`。
形式化陈述：range (f : IntertwiningMap ρ σ) : Subrepresentation σ where toSubmodule
参数：f : IntertwiningMap ρ σ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The range of an intertwining map from `V` to `W` as a subrepresentation of `W`.
-/
def range (f : IntertwiningMap ρ σ) : Subrepresentation σ where
  toSubmodule := LinearMap.range f.toLinearMap
  apply_mem_toSubmodule g {w} := fun ⟨v, hv⟩ ↦ ⟨(ρ g) v, by
    simp [f.isIntertwining, (f.toLinearMap_apply _ _ _).symm.trans hv]⟩

@[simp]
/-
**Representation.IntertwiningMap.mem_range** 是 Mathlib 中的一个引理，位于命名空间 `Representa
tion.IntertwiningMap`。
形式化陈述：mem_range (f : IntertwiningMap ρ σ) (w : W) : w in f.range ↔ exists v, f v
 = w
参数：f : IntertwiningMap ρ σ；w : W。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_range (f : IntertwiningMap ρ σ) (w : W) :
    w ∈ f.range ↔ ∃ v, f v = w := Iff.rfl

/-- The kernel of an intertwining map from `V` to `W` as a subrepresentation of `V`. -/
@[simps]
/-
**Representation.IntertwiningMap.ker** 是 Mathlib 中的一个定义，位于命名空间 `Representation.I
ntertwiningMap`。
形式化陈述：ker (f : IntertwiningMap ρ σ) : Subrepresentation ρ where toSubmodule
参数：f : IntertwiningMap ρ σ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The kernel of an intertwining map from `V` to `W` as a subrepresentation of `V`.
-/
def ker (f : IntertwiningMap ρ σ) : Subrepresentation ρ where
  toSubmodule := LinearMap.ker f.toLinearMap
  apply_mem_toSubmodule g := by simp +contextual [f.isIntertwining]

@[simp]
/-
**Representation.IntertwiningMap.mem_ker** 是 Mathlib 中的一个引理，位于命名空间 `Representati
on.IntertwiningMap`。
形式化陈述：mem_ker (f : IntertwiningMap ρ σ) (v : V) : v in f.ker ↔ f v = 0
参数：f : IntertwiningMap ρ σ；v : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_ker (f : IntertwiningMap ρ σ) (v : V) :
    v ∈ f.ker ↔ f v = 0 := Iff.rfl
/-
**Representation.IntertwiningMap.toLinearMap_sum** 是 Mathlib 中的一个引理，位于命名空间 `Repr
esentation.IntertwiningMap`。
形式化陈述：toLinearMap_sum {ι : Type*} (s : Finset ι) (f : ι -> IntertwiningMap ρ σ) 
: (∑ i in s, f i : IntertwiningMap ρ σ).toLinearMap = ∑ i in s, (f i).toLinearMa
p
参数：s : Finset ι；f : ι -> IntertwiningMap ρ σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
-/
lemma toLinearMap_sum {ι : Type*} (s : Finset ι) (f : ι → IntertwiningMap ρ σ) :
    (∑ i ∈ s, f i : IntertwiningMap ρ σ).toLinearMap = ∑ i ∈ s, (f i).toLinearMap := by
  classical induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, ih]
/-
**Representation.IntertwiningMap.sum_apply** 是 Mathlib 中的一个引理，位于命名空间 `Representa
tion.IntertwiningMap`。
形式化陈述：sum_apply {ι : Type*} (s : Finset ι) (f : ι -> IntertwiningMap ρ σ) (v : V
) : (∑ i in s, f i) v = ∑ i in s, f i v
参数：s : Finset ι；f : ι -> IntertwiningMap ρ σ；v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Representation.IntertwiningMap.toLinearMap_apply`：toLinearMap_apply (f :
 IntertwiningMap ρ σ) (v : V) : f.toLinearMap v = f v
· 使用引理 `Representation.IntertwiningMap.toLinearMap_sum`：toLinearMap_sum {ι : Typ
e*} (s : Finset ι) (f : ι -> IntertwiningMap ρ σ) : (∑ i in s, f i : Intertwinin
gMap ρ σ).toLinearMap = ∑ i in s, (f…
· 使用定理 `LinearMap.sum_apply`：sum_apply (t : Finset ι) (f : ι -> M ->ₛₗ[σ₁₂] M₂) 
(b : M) : (∑ d in t, f d) b = ∑ d in t, f d b
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sum_apply {ι : Type*} (s : Finset ι) (f : ι → IntertwiningMap ρ σ) (v : V) :
    (∑ i ∈ s, f i) v = ∑ i ∈ s, f i v := by
  simp [← toLinearMap_apply _ _ (∑ _ ∈ s, _), toLinearMap_sum, LinearMap.sum_apply]

section group

variable {V W P : Type*} [AddCommMonoid V] [AddCommGroup W]
  [AddCommGroup P] [Module A V] [Module A W] [Module A P] (ρ : Representation A G V)
  (σ : Representation A G W) (τ : Representation A G P) (f : V →ₗ[A] W)

/-
**Representation.IntertwiningMap.** 是 Mathlib 中的一个实例，位于命名空间 `Representation.Inte
rtwiningMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg (IntertwiningMap ρ σ) :=
  ⟨fun f ↦ ⟨-f.toLinearMap, by simp [LinearMap.neg_comp, f.2]⟩⟩

@[simp]
/-
**Representation.IntertwiningMap.coe_neg** 是 Mathlib 中的一个引理，位于命名空间 `Representati
on.IntertwiningMap`。
形式化陈述：coe_neg (f : IntertwiningMap ρ σ) : ((-f : IntertwiningMap ρ σ) : V -> W) 
= -f
参数：f : IntertwiningMap ρ σ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_neg (f : IntertwiningMap ρ σ) : ((-f : IntertwiningMap ρ σ) : V → W) = -f := rfl
/-
**Representation.IntertwiningMap.** 是 Mathlib 中的一个实例，位于命名空间 `Representation.Inte
rtwiningMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sub (IntertwiningMap ρ σ) :=
  ⟨fun f g ↦ ⟨f.toLinearMap - g.toLinearMap, by
    simp [LinearMap.sub_comp, LinearMap.comp_sub, f.2, g.2]⟩⟩
/-
**Representation.IntertwiningMap.coe_sub** 是 Mathlib 中的一个定理，位于命名空间 `Representati
on.IntertwiningMap`。
形式化陈述：∀ {A : Type u_1} {G : Type u_2} [inst : Semiring A] [inst_1 : Monoid G] {V
 : Type u_6} {W : Type u_7}   [inst_2 : AddCommMonoid V] [inst_3 : AddCommGroup 
W] [inst_4 : _root_.Module A V] [inst_5 : _root_.Module A W]   (ρ : Representati
on A G V) (σ : Representation A G W) (f g : ρ.IntertwiningMap σ), ⇑(f - g) = ⇑f 
- ⇑g
参数：ρ : Representation A G V；σ : Representation A G W；f g : ρ.IntertwiningMap σ；f
 - g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_sub (f g : IntertwiningMap ρ σ) :
    ((f - g : IntertwiningMap ρ σ) : V → W) = f - g := rfl

@[simp]
/-
**Representation.IntertwiningMap.sub_toLinearMap** 是 Mathlib 中的一个引理，位于命名空间 `Repr
esentation.IntertwiningMap`。
形式化陈述：sub_toLinearMap (f g : IntertwiningMap ρ σ) : (f - g).toLinearMap = f.toLi
nearMap - g.toLinearMap
参数：f g : IntertwiningMap ρ σ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sub_toLinearMap (f g : IntertwiningMap ρ σ) :
    (f - g).toLinearMap = f.toLinearMap - g.toLinearMap := rfl
/-
**Representation.IntertwiningMap.** 是 Mathlib 中的一个实例，位于命名空间 `Representation.Inte
rtwiningMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul ℤ (IntertwiningMap ρ σ) :=
  ⟨fun z f ↦ ⟨z • f.toLinearMap, by simp [LinearMap.smul_comp, LinearMap.comp_smul, f.2]⟩⟩
/-
**Representation.IntertwiningMap.coe_zsmul** 是 Mathlib 中的一个定理，位于命名空间 `Representa
tion.IntertwiningMap`。
形式化陈述：∀ {A : Type u_1} {G : Type u_2} [inst : Semiring A] [inst_1 : Monoid G] {V
 : Type u_6} {W : Type u_7}   [inst_2 : AddCommMonoid V] [inst_3 : AddCommGroup 
W] [inst_4 : _root_.Module A V] [inst_5 : _root_.Module A W]   (ρ : Representati
on A G V) (σ : Representation A G W) (f : ρ.IntertwiningMap σ) (z : ℤ), ⇑(z • f)
 = z • ⇑f
参数：ρ : Representation A G V；σ : Representation A G W；f : ρ.IntertwiningMap σ；z :
 ℤ；z • f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_zsmul (f : IntertwiningMap ρ σ) (z : ℤ) :
    ((z • f : IntertwiningMap ρ σ) : V → W) = z • f := rfl
/-
**Representation.IntertwiningMap.** 是 Mathlib 中的一个实例，位于命名空间 `Representation.Inte
rtwiningMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommGroup (IntertwiningMap ρ σ) :=
  fast_instance%
  DFunLike.coe_injective.addCommGroup _ (coe_zero ρ σ) (coe_add ρ σ) (coe_neg ρ σ) (coe_sub ρ σ)
    (coe_nsmul ρ σ) (coe_zsmul ρ σ)

end group

/-- A coercion from intertwining maps to additive monoid homomorphisms. -/
/-
**Representation.IntertwiningMap.coeFnAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `Re
presentation.IntertwiningMap`。
形式化陈述：coeFnAddMonoidHom : IntertwiningMap ρ σ ->+ V -> W where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Representation.IntertwiningMap.coe_zero`：∀ {A : Type u_1} {G : Type u_2}
 {V : Type u_3} {W : Type u_4} [inst : Semiring A] [inst_1 : Monoid G]   [inst_2
 : AddCommMonoid V] [inst_3 :…
· 使用定理 `Representation.IntertwiningMap.coe_add`：∀ {A : Type u_1} {G : Type u_2} 
{V : Type u_3} {W : Type u_4} [inst : Semiring A] [inst_1 : Monoid G]   [inst_2 
: AddCommMonoid V] [inst_3 :…

--- 原说明 ---
A coercion from intertwining maps to additive monoid homomorphisms.
-/
def coeFnAddMonoidHom : IntertwiningMap ρ σ →+ V → W where
  toFun := (⇑)
  map_zero' := coe_zero ρ σ
  map_add' := coe_add ρ σ

/-- The identity map, considered as an intertwining map from a representation to itself. -/
/-
**Representation.IntertwiningMap.id** 是 Mathlib 中的一个定义，位于命名空间 `Representation.In
tertwiningMap`。
形式化陈述：id : IntertwiningMap ρ ρ where toLinearMap
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity map, considered as an intertwining map from a representation to its
elf.
-/
def id : IntertwiningMap ρ ρ where
  toLinearMap := LinearMap.id
  isIntertwining' := by simp

@[simp]
/-
**Representation.IntertwiningMap.toLinearMap_id** 是 Mathlib 中的一个引理，位于命名空间 `Repre
sentation.IntertwiningMap`。
形式化陈述：toLinearMap_id : (id ρ).toLinearMap = LinearMap.id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toLinearMap_id : (id ρ).toLinearMap = LinearMap.id := rfl

@[simp]
/-
**Representation.IntertwiningMap.id_apply** 是 Mathlib 中的一个引理，位于命名空间 `Representat
ion.IntertwiningMap`。
形式化陈述：id_apply (v : V) : id ρ v = v
参数：v : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma id_apply (v : V) : id ρ v = v := rfl

variable {ρ σ τ} in
/-- Composition of intertwining maps.

A convenience variant of `IntertwiningMap.llcomp` for use in dot notation. -/
/-
**Representation.IntertwiningMap.comp** 是 Mathlib 中的一个定义，位于命名空间 `Representation.
IntertwiningMap`。
形式化陈述：comp (f : IntertwiningMap σ τ) (g : IntertwiningMap ρ σ) : IntertwiningMap
 ρ τ where __
参数：f : IntertwiningMap σ τ；g : IntertwiningMap ρ σ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of intertwining maps.

A convenience variant of `IntertwiningMap.llcomp` for use in dot notation.
-/
def comp (f : IntertwiningMap σ τ) (g : IntertwiningMap ρ σ) : IntertwiningMap ρ τ where
  __ := f.toLinearMap ∘ₗ g.toLinearMap
  isIntertwining' := by simp [LinearMap.comp_assoc, g.2, f.isIntertwining_assoc]

@[simp]
/-
**Representation.IntertwiningMap.comp_toLinearMap** 是 Mathlib 中的一个引理，位于命名空间 `Rep
resentation.IntertwiningMap`。
形式化陈述：comp_toLinearMap (f : IntertwiningMap σ τ) (g : IntertwiningMap ρ σ) : (co
mp f g).toLinearMap = f.toLinearMap.comp g.toLinearMap
参数：f : IntertwiningMap σ τ；g : IntertwiningMap ρ σ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_toLinearMap (f : IntertwiningMap σ τ) (g : IntertwiningMap ρ σ) :
    (comp f g).toLinearMap = f.toLinearMap.comp g.toLinearMap := rfl

@[simp]
/-
**Representation.IntertwiningMap.comp_apply** 是 Mathlib 中的一个引理，位于命名空间 `Represent
ation.IntertwiningMap`。
形式化陈述：comp_apply (f : IntertwiningMap σ τ) (g : IntertwiningMap ρ σ) (v : V) : c
omp f g v = f (g v)
参数：f : IntertwiningMap σ τ；g : IntertwiningMap ρ σ；v : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_apply (f : IntertwiningMap σ τ) (g : IntertwiningMap ρ σ) (v : V) :
    comp f g v = f (g v) := rfl
/-
**Representation.IntertwiningMap.comp_add** 是 Mathlib 中的一个引理，位于命名空间 `Representat
ion.IntertwiningMap`。
形式化陈述：comp_add (f₁ f₂ : IntertwiningMap σ τ) (g : IntertwiningMap ρ σ) : (f₁ + f
₂).comp g = comp f₁ g + comp f₂ g
参数：f₁ f₂ : IntertwiningMap σ τ；g : IntertwiningMap ρ σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Representation.IntertwiningMap.ext`：ext {f g : IntertwiningMap ρ σ} (h :
 f.toLinearMap = g.toLinearMap) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_add (f₁ f₂ : IntertwiningMap σ τ) (g : IntertwiningMap ρ σ) :
    (f₁ + f₂).comp g = comp f₁ g + comp f₂ g := by ext1; simp [LinearMap.add_comp]
/-
**Representation.IntertwiningMap.add_comp** 是 Mathlib 中的一个引理，位于命名空间 `Representat
ion.IntertwiningMap`。
形式化陈述：add_comp (f : IntertwiningMap σ τ) (g₁ g₂ : IntertwiningMap ρ σ) : comp f 
(g₁ + g₂) = comp f g₁ + comp f g₂
参数：f : IntertwiningMap σ τ；g₁ g₂ : IntertwiningMap ρ σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Representation.IntertwiningMap.ext`：ext {f g : IntertwiningMap ρ σ} (h :
 f.toLinearMap = g.toLinearMap) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp_add`：comp_add (f g : M ->ₛₗ[σ₁₂] M₂) (h : M₂ ->ₛₗ[σ₂₃] M₃
) : (h.comp (f + g) : M ->ₛₗ[σ₁₃] M₃) = h.comp f + h.comp g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma add_comp (f : IntertwiningMap σ τ) (g₁ g₂ : IntertwiningMap ρ σ) :
    comp f (g₁ + g₂) = comp f g₁ + comp f g₂ := by ext1; simp [LinearMap.comp_add]

variable (A) in
/-- The projection of a product representation onto its first component is an intertwining map. -/
/-
**Representation.IntertwiningMap.fst** 是 Mathlib 中的一个定义，位于命名空间 `Representation.I
ntertwiningMap`。
形式化陈述：fst : IntertwiningMap (ρ.prod σ) ρ where toLinearMap
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection of a product representation onto its first component is an intert
wining map.
-/
def fst : IntertwiningMap (ρ.prod σ) ρ where
  toLinearMap := LinearMap.fst A V W
  isIntertwining' _ := LinearMap.ext <| by simp

variable (A) in
/-- The projection of a product representation onto its second component is an intertwining map. -/
/-
**Representation.IntertwiningMap.snd** 是 Mathlib 中的一个定义，位于命名空间 `Representation.I
ntertwiningMap`。
形式化陈述：snd : IntertwiningMap (ρ.prod σ) σ where toLinearMap
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection of a product representation onto its second component is an inter
twining map.
-/
def snd : IntertwiningMap (ρ.prod σ) σ where
  toLinearMap := LinearMap.snd A V W
  isIntertwining' _ := LinearMap.ext <| by simp

@[simp]
/-
**Representation.IntertwiningMap.fst_apply** 是 Mathlib 中的一个引理，位于命名空间 `Representa
tion.IntertwiningMap`。
形式化陈述：fst_apply (v : V × W) : fst A ρ σ v = v.1
参数：v : V × W。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fst_apply (v : V × W) : fst A ρ σ v = v.1 := rfl

@[simp]
/-
**Representation.IntertwiningMap.snd_apply** 是 Mathlib 中的一个引理，位于命名空间 `Representa
tion.IntertwiningMap`。
形式化陈述：snd_apply (v : V × W) : snd A ρ σ v = v.2
参数：v : V × W。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma snd_apply (v : V × W) : snd A ρ σ v = v.2 := rfl
/-
**Representation.IntertwiningMap.coe_fst** 是 Mathlib 中的一个定理，位于命名空间 `Representati
on.IntertwiningMap`。
形式化陈述：∀ {A : Type u_1} {G : Type u_2} {V : Type u_3} {W : Type u_4} [inst : Semi
ring A] [inst_1 : Monoid G]   [inst_2 : AddCommMonoid V] [inst_3 : AddCommMonoid
 W] [inst_4 : _root_.Module A V] [inst_5 : _root_.Module A W]   (ρ : Representat
ion A G V) (σ : Representation A G W), ⇑(Representation.IntertwiningMap.fst A ρ 
σ) = Prod.fst
参数：ρ : Representation A G V；σ : Representation A G W；Representation.Intertwining
Map.fst A ρ σ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_fst : ⇑(fst A ρ σ) = Prod.fst := rfl
/-
**Representation.IntertwiningMap.coe_snd** 是 Mathlib 中的一个定理，位于命名空间 `Representati
on.IntertwiningMap`。
形式化陈述：∀ {A : Type u_1} {G : Type u_2} {V : Type u_3} {W : Type u_4} [inst : Semi
ring A] [inst_1 : Monoid G]   [inst_2 : AddCommMonoid V] [inst_3 : AddCommMonoid
 W] [inst_4 : _root_.Module A V] [inst_5 : _root_.Module A W]   (ρ : Representat
ion A G V) (σ : Representation A G W), ⇑(Representation.IntertwiningMap.snd A ρ 
σ) = Prod.snd
参数：ρ : Representation A G V；σ : Representation A G W；Representation.Intertwining
Map.snd A ρ σ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_snd : ⇑(snd A ρ σ) = Prod.snd := rfl
/-
**Representation.IntertwiningMap.fst_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Repre
sentation.IntertwiningMap`。
形式化陈述：fst_surjective : Function.Surjective (fst A ρ σ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.fst_surjective`：fst_surjective : Function.Surjective (fst R M 
M₂)
-/
lemma fst_surjective : Function.Surjective (fst A ρ σ) := LinearMap.fst_surjective
/-
**Representation.IntertwiningMap.snd_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Repre
sentation.IntertwiningMap`。
形式化陈述：snd_surjective : Function.Surjective (snd A ρ σ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.snd_surjective`：snd_surjective : Function.Surjective (snd R M 
M₂)
-/
lemma snd_surjective : Function.Surjective (snd A ρ σ) := LinearMap.snd_surjective

section prod

variable {ρ σ τ}
/-- The product of two intertwining maps is an intertwining map. -/
/-
**Representation.IntertwiningMap.prod** 是 Mathlib 中的一个定义，位于命名空间 `Representation.
IntertwiningMap`。
形式化陈述：prod (f : IntertwiningMap ρ σ) (g : IntertwiningMap ρ τ) : IntertwiningMap
 ρ (σ.prod τ) where toLinearMap
参数：f : IntertwiningMap ρ σ；g : IntertwiningMap ρ τ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of two intertwining maps is an intertwining map.
-/
def prod (f : IntertwiningMap ρ σ) (g : IntertwiningMap ρ τ) : IntertwiningMap ρ (σ.prod τ) where
  toLinearMap := f.toLinearMap.prod g.toLinearMap
  isIntertwining' _ := LinearMap.ext <| by simp [f.isIntertwining, g.isIntertwining]

@[simp]
/-
**Representation.IntertwiningMap.fst_prod** 是 Mathlib 中的一个引理，位于命名空间 `Representat
ion.IntertwiningMap`。
形式化陈述：fst_prod (f : IntertwiningMap ρ σ) (g : IntertwiningMap ρ τ) : (fst A σ τ)
.comp (prod f g) = f
参数：f : IntertwiningMap ρ σ；g : IntertwiningMap ρ τ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Representation.IntertwiningMap.ext`：ext {f g : IntertwiningMap ρ σ} (h :
 f.toLinearMap = g.toLinearMap) : f = g
· 使用定理 `LinearMap.fst_prod`：fst_prod (f : M ->ₗ[R] M₂) (g : M ->ₗ[R] M₃) : (fst 
R M₂ M₃).comp (prod f g) = f
-/
lemma fst_prod (f : IntertwiningMap ρ σ) (g : IntertwiningMap ρ τ) :
    (fst A σ τ).comp (prod f g) = f := IntertwiningMap.ext <| LinearMap.fst_prod _ _

@[simp]
/-
**Representation.IntertwiningMap.snd_prod** 是 Mathlib 中的一个引理，位于命名空间 `Representat
ion.IntertwiningMap`。
形式化陈述：snd_prod (f : IntertwiningMap ρ σ) (g : IntertwiningMap ρ τ) : (snd A σ τ)
.comp (prod f g) = g
参数：f : IntertwiningMap ρ σ；g : IntertwiningMap ρ τ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Representation.IntertwiningMap.ext`：ext {f g : IntertwiningMap ρ σ} (h :
 f.toLinearMap = g.toLinearMap) : f = g
· 使用定理 `LinearMap.snd_prod`：snd_prod (f : M ->ₗ[R] M₂) (g : M ->ₗ[R] M₃) : (snd 
R M₂ M₃).comp (prod f g) = g
-/
lemma snd_prod (f : IntertwiningMap ρ σ) (g : IntertwiningMap ρ τ) :
    (snd A σ τ).comp (prod f g) = g := IntertwiningMap.ext <| LinearMap.snd_prod _ _
/-
**Representation.IntertwiningMap.prod_comp** 是 Mathlib 中的一个引理，位于命名空间 `Representa
tion.IntertwiningMap`。
形式化陈述：prod_comp (X : Type*) [AddCommMonoid X] [Module A X] {π : Representation A
 G X} (f : IntertwiningMap ρ σ) (g₁ : IntertwiningMap σ τ) (g₂ : IntertwiningMap
 σ π) : (prod g₁ g₂).comp f = prod (g₁.comp f) (g₂.comp f)
参数：X : Type*；f : IntertwiningMap ρ σ；g₁ : IntertwiningMap σ τ；g₂ : IntertwiningM
ap σ π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Representation.IntertwiningMap.ext`：ext {f g : IntertwiningMap ρ σ} (h :
 f.toLinearMap = g.toLinearMap) : f = g
· 使用定理 `LinearMap.prod_comp`：prod_comp (f : M₂ ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₄) (h 
: M ->ₗ[R] M₂) : (f.prod g).comp h = (f.comp h).prod (g.comp h)
-/
lemma prod_comp (X : Type*) [AddCommMonoid X] [Module A X] {π : Representation A G X}
    (f : IntertwiningMap ρ σ) (g₁ : IntertwiningMap σ τ) (g₂ : IntertwiningMap σ π) :
    (prod g₁ g₂).comp f = prod (g₁.comp f) (g₂.comp f) :=
  IntertwiningMap.ext <| LinearMap.prod_comp ..

variable (A ρ σ) in
/-- The left inclusion of a product representation is an intertwining map. -/
/-
**Representation.IntertwiningMap.inl** 是 Mathlib 中的一个定义，位于命名空间 `Representation.I
ntertwiningMap`。
形式化陈述：inl : IntertwiningMap ρ (ρ.prod σ)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left inclusion of a product representation is an intertwining map.
-/
def inl : IntertwiningMap ρ (ρ.prod σ) := prod (id ρ) 0

variable (A ρ σ) in
/-- The right inclusion of a product representation is an intertwining map. -/
/-
**Representation.IntertwiningMap.inr** 是 Mathlib 中的一个定义，位于命名空间 `Representation.I
ntertwiningMap`。
形式化陈述：inr : IntertwiningMap σ (ρ.prod σ)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right inclusion of a product representation is an intertwining map.
-/
def inr : IntertwiningMap σ (ρ.prod σ) := prod (0 : IntertwiningMap σ ρ) (id σ)
/-
**Representation.IntertwiningMap.range_inl** 是 Mathlib 中的一个引理，位于命名空间 `Representa
tion.IntertwiningMap`。
形式化陈述：range_inl : (inl A ρ σ).range = (snd A ρ σ).ker
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subrepresentation.ext`：∀ {A : Type u_1} {G : Type u_2} {W : Type u_3} {i
nst : Semiring A} {inst_1 : Monoid G} {inst_2 : AddCommMonoid W}   {inst_3 : _ro
ot_.Module …
· 使用定理 `LinearMap.range_inl`：range_inl : range (inl R M M₂) = ker (snd R M M₂)
-/
lemma range_inl : (inl A ρ σ).range = (snd A ρ σ).ker :=
  Subrepresentation.ext <| LinearMap.range_inl ..
/-
**Representation.IntertwiningMap.range_inr** 是 Mathlib 中的一个引理，位于命名空间 `Representa
tion.IntertwiningMap`。
形式化陈述：range_inr : (inr A ρ σ).range = (fst A ρ σ).ker
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subrepresentation.ext`：∀ {A : Type u_1} {G : Type u_2} {W : Type u_3} {i
nst : Semiring A} {inst_1 : Monoid G} {inst_2 : AddCommMonoid W}   {inst_3 : _ro
ot_.Module …
· 使用定理 `LinearMap.range_inr`：range_inr : range (inr R M M₂) = ker (fst R M M₂)
-/
lemma range_inr : (inr A ρ σ).range = (fst A ρ σ).ker :=
  Subrepresentation.ext <| LinearMap.range_inr ..
/-
**Representation.IntertwiningMap.fst_comp_inl** 是 Mathlib 中的一个定理，位于命名空间 `Represe
ntation.IntertwiningMap`。
形式化陈述：∀ {A : Type u_1} {G : Type u_2} {V : Type u_3} {W : Type u_4} [inst : Semi
ring A] [inst_1 : Monoid G]   [inst_2 : AddCommMonoid V] [inst_3 : AddCommMonoid
 W] [inst_4 : _root_.Module A V] [inst_5 : _root_.Module A W]   {ρ : Representat
ion A G V} {σ : Representation A G W},   (Representation.IntertwiningMap.fst A ρ
 σ).comp (Representation.IntertwiningMap.inl A ρ σ) =     Representation.Intertw
iningMap.id ρ
参数：Representation.IntertwiningMap.fst A ρ σ；Representation.IntertwiningMap.inl A
 ρ σ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Representation.IntertwiningMap.ext`：ext {f g : IntertwiningMap ρ σ} (h :
 f.toLinearMap = g.toLinearMap) : f = g
· 使用定理 `LinearMap.fst_comp_inl`：∀ (R : Type u) (M : Type v) (M₂ : Type w) [inst 
: Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : AddCommMonoid M₂]   [inst_3 :
 _root_.Modu…
-/
@[simp] lemma fst_comp_inl : (fst A ρ σ).comp (inl A ρ σ) = id ρ :=
  IntertwiningMap.ext <| LinearMap.fst_comp_inl ..
/-
**Representation.IntertwiningMap.snd_comp_inl** 是 Mathlib 中的一个定理，位于命名空间 `Represe
ntation.IntertwiningMap`。
形式化陈述：∀ {A : Type u_1} {G : Type u_2} {V : Type u_3} {W : Type u_4} [inst : Semi
ring A] [inst_1 : Monoid G]   [inst_2 : AddCommMonoid V] [inst_3 : AddCommMonoid
 W] [inst_4 : _root_.Module A V] [inst_5 : _root_.Module A W]   {ρ : Representat
ion A G V} {σ : Representation A G W},   (Representation.IntertwiningMap.snd A ρ
 σ).comp (Representation.IntertwiningMap.inl A ρ σ) = 0
参数：Representation.IntertwiningMap.snd A ρ σ；Representation.IntertwiningMap.inl A
 ρ σ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Representation.IntertwiningMap.ext`：ext {f g : IntertwiningMap ρ σ} (h :
 f.toLinearMap = g.toLinearMap) : f = g
· 使用定理 `LinearMap.snd_comp_inl`：∀ (R : Type u) (M : Type v) (M₂ : Type w) [inst 
: Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : AddCommMonoid M₂]   [inst_3 :
 _root_.Modu…
-/
@[simp] lemma snd_comp_inl : (snd A ρ σ).comp (inl A ρ σ) = 0 :=
  IntertwiningMap.ext <| LinearMap.snd_comp_inl ..
/-
**Representation.IntertwiningMap.fst_comp_inr** 是 Mathlib 中的一个定理，位于命名空间 `Represe
ntation.IntertwiningMap`。
形式化陈述：∀ {A : Type u_1} {G : Type u_2} {V : Type u_3} {W : Type u_4} [inst : Semi
ring A] [inst_1 : Monoid G]   [inst_2 : AddCommMonoid V] [inst_3 : AddCommMonoid
 W] [inst_4 : _root_.Module A V] [inst_5 : _root_.Module A W]   {ρ : Representat
ion A G V} {σ : Representation A G W},   (Representation.IntertwiningMap.fst A ρ
 σ).comp (Representation.IntertwiningMap.inr A ρ σ) = 0
参数：Representation.IntertwiningMap.fst A ρ σ；Representation.IntertwiningMap.inr A
 ρ σ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Representation.IntertwiningMap.ext`：ext {f g : IntertwiningMap ρ σ} (h :
 f.toLinearMap = g.toLinearMap) : f = g
· 使用定理 `LinearMap.fst_comp_inr`：∀ (R : Type u) (M : Type v) (M₂ : Type w) [inst 
: Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : AddCommMonoid M₂]   [inst_3 :
 _root_.Modu…
-/
@[simp] lemma fst_comp_inr : (fst A ρ σ).comp (inr A ρ σ) = 0 :=
  IntertwiningMap.ext <| LinearMap.fst_comp_inr ..
/-
**Representation.IntertwiningMap.snd_comp_inr** 是 Mathlib 中的一个定理，位于命名空间 `Represe
ntation.IntertwiningMap`。
形式化陈述：∀ {A : Type u_1} {G : Type u_2} {V : Type u_3} {W : Type u_4} [inst : Semi
ring A] [inst_1 : Monoid G]   [inst_2 : AddCommMonoid V] [inst_3 : AddCommMonoid
 W] [inst_4 : _root_.Module A V] [inst_5 : _root_.Module A W]   {ρ : Representat
ion A G V} {σ : Representation A G W},   (Representation.IntertwiningMap.snd A ρ
 σ).comp (Representation.IntertwiningMap.inr A ρ σ) =     Representation.Intertw
iningMap.id σ
参数：Representation.IntertwiningMap.snd A ρ σ；Representation.IntertwiningMap.inr A
 ρ σ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Representation.IntertwiningMap.ext`：ext {f g : IntertwiningMap ρ σ} (h :
 f.toLinearMap = g.toLinearMap) : f = g
· 使用定理 `LinearMap.snd_comp_inr`：∀ (R : Type u) (M : Type v) (M₂ : Type w) [inst 
: Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : AddCommMonoid M₂]   [inst_3 :
 _root_.Modu…
-/
@[simp] lemma snd_comp_inr : (snd A ρ σ).comp (inr A ρ σ) = id σ :=
  IntertwiningMap.ext <| LinearMap.snd_comp_inr ..
/-
**Representation.IntertwiningMap.coprod_inl_inr** 是 Mathlib 中的一个定理，位于命名空间 `Repre
sentation.IntertwiningMap`。
形式化陈述：∀ {A : Type u_1} {G : Type u_2} {V : Type u_3} {W : Type u_4} [inst : Semi
ring A] [inst_1 : Monoid G]   [inst_2 : AddCommMonoid V] [inst_3 : AddCommMonoid
 W] [inst_4 : _root_.Module A V] [inst_5 : _root_.Module A W]   {ρ : Representat
ion A G V} {σ : Representation A G W},   (Representation.IntertwiningMap.inl A ρ
 σ).comp (Representation.IntertwiningMap.fst A ρ σ) +       (Representation.Inte
rtwiningMap.inr A ρ σ).comp (Representation.IntertwiningMap.snd A ρ σ) =     Rep
resentation.IntertwiningMap.id (ρ.prod σ)
参数：Representation.IntertwiningMap.inl A ρ σ；Representation.IntertwiningMap.fst A
 ρ σ；Representation.IntertwiningMap.inr A ρ σ；Representation.IntertwiningMap.snd
 A ρ σ；ρ.prod σ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Representation.IntertwiningMap.ext`：ext {f g : IntertwiningMap ρ σ} (h :
 f.toLinearMap = g.toLinearMap) : f = g
· 使用定理 `LinearMap.coprod_inl_inr`：coprod_inl_inr : coprod (inl R M M₂) (inr R M 
M₂) = LinearMap.id
-/
@[simp] lemma coprod_inl_inr : (inl A ρ σ).comp (fst A ρ σ) + (inr A ρ σ).comp (snd A ρ σ) =
    .id _ := IntertwiningMap.ext <| LinearMap.coprod_inl_inr

end prod

end IntertwiningMap

/-- Equivalence between representations is a bijective intertwining map. -/
/-
**Representation.Equiv** 是 Mathlib 中的一个归纳类型，位于命名空间 `Representation`。
形式化陈述：{A : Type u_1} →   {G : Type u_2} →     {V : Type u_3} →       {W : Type u
_4} →         [inst : Semiring A] →           [inst_1 : Monoid G] →             
[inst_2 : AddCommMonoid V] →               [inst_3 : AddCommMonoid W] →         
        [inst_4 : _root_.Module A V] →                   [inst_5 : _root_.Module
 A W] → Representation A G V → Representation A G W → Type (max u_3 u_4)
参数：max u_3 u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence between representations is a bijective intertwining map.
-/
structure Equiv extends IntertwiningMap ρ σ, V ≃ₗ[A] W where
  mk' ::

attribute [coe] Equiv.toIntertwiningMap

/-- Underlying linear isomorphism of an equivalence of representations. -/
add_decl_doc Equiv.toLinearEquiv

/-- The intertwining map underlying an equivalence of representations. -/
add_decl_doc Equiv.toIntertwiningMap

namespace Equiv

variable {ρ σ} (φ : Equiv ρ σ)

/-- An `Equiv` between representations could be built from a `LinearEquiv` and an assumption
  proving the `G`-equivariance. -/
/-
**Representation.Equiv.mk** 是 Mathlib 中的一个定义，位于命名空间 `Representation.Equiv`。
形式化陈述：mk (e : V ≃ₗ[A] W) (he : forall g, e ∘ₗ (ρ g) = (σ g) ∘ₗ e) : ρ.Equiv σ wh
ere __
参数：e : V ≃ₗ[A] W；he : forall g, e ∘ₗ (ρ g) = (σ g) ∘ₗ e。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `Equiv` between representations could be built from a `LinearEquiv` and an as
sumption
  proving the `G`-equivariance.
-/
def mk (e : V ≃ₗ[A] W) (he : ∀ g, e ∘ₗ (ρ g) = (σ g) ∘ₗ e) : ρ.Equiv σ where
  __ := e
  isIntertwining' := he
/-
**Representation.Equiv.toLinearEquiv_mk'** 是 Mathlib 中的一个引理，位于命名空间 `Representati
on.Equiv`。
形式化陈述：toLinearEquiv_mk' {e : V ≃ₗ[A] W} (he : forall g, e ∘ₗ (ρ g) = (σ g) ∘ₗ e)
 : (mk e he).toLinearEquiv = e
参数：he : forall g, e ∘ₗ (ρ g) = (σ g) ∘ₗ e。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toLinearEquiv_mk' {e : V ≃ₗ[A] W} (he : ∀ g, e ∘ₗ (ρ g) = (σ g) ∘ₗ e) :
    (mk e he).toLinearEquiv = e := rfl
/-
**Representation.Equiv.toIntertwiningMap_mk'** 是 Mathlib 中的一个引理，位于命名空间 `Represen
tation.Equiv`。
形式化陈述：toIntertwiningMap_mk' (e : V ≃ₗ[A] W) (he : forall g, e ∘ₗ (ρ g) = (σ g) ∘
ₗ e) : (mk e he).toIntertwiningMap = ⟨e.toLinearMap, he⟩
参数：e : V ≃ₗ[A] W；he : forall g, e ∘ₗ (ρ g) = (σ g) ∘ₗ e。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toIntertwiningMap_mk' (e : V ≃ₗ[A] W) (he : ∀ g, e ∘ₗ (ρ g) = (σ g) ∘ₗ e) :
    (mk e he).toIntertwiningMap = ⟨e.toLinearMap, he⟩ := rfl

@[simp]
/-
**Representation.Equiv.toLinearMap_mk'** 是 Mathlib 中的一个引理，位于命名空间 `Representation
.Equiv`。
形式化陈述：toLinearMap_mk' (e : V ≃ₗ[A] W) (he : forall g, e ∘ₗ (ρ g) = (σ g) ∘ₗ e) :
 (mk e he).toLinearMap = e.toLinearMap
参数：e : V ≃ₗ[A] W；he : forall g, e ∘ₗ (ρ g) = (σ g) ∘ₗ e。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toLinearMap_mk' (e : V ≃ₗ[A] W) (he : ∀ g, e ∘ₗ (ρ g) = (σ g) ∘ₗ e) :
    (mk e he).toLinearMap = e.toLinearMap := rfl
/-
**Representation.Equiv.toLinearEquiv_injective** 是 Mathlib 中的一个引理，位于命名空间 `Repres
entation.Equiv`。
形式化陈述：toLinearEquiv_injective : Function.Injective (toLinearEquiv : (σ.Equiv ρ) 
-> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Representation.Equiv.mk'.injEq`：∀ {A : Type u_1} {G : Type u_2} {V : Typ
e u_3} {W : Type u_4} [inst : Semiring A] [inst_1 : Monoid G]   [inst_2 : AddCom
mMonoid V] [inst_3 :…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.mk.injEq`：∀ {R : Type u_14} {S : Type u_15} [inst : Semiring
 R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPai
r σ σ'] [i…
· 使用定理 `Representation.Equiv.left_inv`：∀ {A : Type u_1} {G : Type u_2} {V : Type
 u_3} {W : Type u_4} [inst : Semiring A] [inst_1 : Monoid G]   [inst_2 : AddComm
Monoid V] [inst_3 :…
· 使用定理 `Representation.Equiv.right_inv`：∀ {A : Type u_1} {G : Type u_2} {V : Typ
e u_3} {W : Type u_4} [inst : Semiring A] [inst_1 : Monoid G]   [inst_2 : AddCom
mMonoid V] [inst_3 :…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma toLinearEquiv_injective : Function.Injective (toLinearEquiv : (σ.Equiv ρ) → _) :=
  fun φ ψ h ↦ by cases φ; cases ψ; simpa [IntertwiningMap.ext_iff] using h
/-
**Representation.Equiv.toLinearEquiv_inj** 是 Mathlib 中的一个引理，位于命名空间 `Representati
on.Equiv`。
形式化陈述：toLinearEquiv_inj (φ ψ : σ.Equiv ρ) : φ.toLinearEquiv = ψ.toLinearEquiv ↔ 
φ = ψ
参数：φ ψ : σ.Equiv ρ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `Representation.Equiv.toLinearEquiv_injective`：toLinearEquiv_injective : 
Function.Injective (toLinearEquiv : (σ.Equiv ρ) -> _)
-/
lemma toLinearEquiv_inj (φ ψ : σ.Equiv ρ) : φ.toLinearEquiv = ψ.toLinearEquiv ↔ φ = ψ :=
  toLinearEquiv_injective.eq_iff
/-
**Representation.Equiv.** 是 Mathlib 中的一个实例，位于命名空间 `Representation.Equiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : EquivLike (Equiv ρ σ) V W where
  coe φ := φ.toLinearEquiv
  inv φ := φ.invFun
  left_inv e := e.left_inv
  right_inv e := e.right_inv
  coe_injective' φ ψ h1 h2 := by
    cases φ; cases ψ
    simp_all [IntertwiningMap.ext_iff]
/-
**Representation.Equiv.** 是 Mathlib 中的一个实例，位于命名空间 `Representation.Equiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LinearEquivClass (σ.Equiv ρ) A W V where
  map_add f := f.map_add
  map_smulₛₗ f := f.map_smul

@[simp]
/-
**Representation.Equiv.mk_apply** 是 Mathlib 中的一个引理，位于命名空间 `Representation.Equiv`
。
形式化陈述：mk_apply {e : V ≃ₗ[A] W} (he : forall g, e ∘ₗ (ρ g) = (σ g) ∘ₗ e) (v : V) 
: (mk e he) v = e v
参数：he : forall g, e ∘ₗ (ρ g) = (σ g) ∘ₗ e；v : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk_apply {e : V ≃ₗ[A] W} (he : ∀ g, e ∘ₗ (ρ g) = (σ g) ∘ₗ e) (v : V) :
    (mk e he) v = e v := rfl

@[ext]
/-
**Representation.Equiv.ext** 是 Mathlib 中的一个引理，位于命名空间 `Representation.Equiv`。
形式化陈述：ext {φ ψ : Equiv ρ σ} (h : (φ : V -> W) = ψ) : φ = ψ
参数：h : (φ : V -> W) = ψ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Representation.Equiv.mk'.injEq`：∀ {A : Type u_1} {G : Type u_2} {V : Typ
e u_3} {W : Type u_4} [inst : Semiring A] [inst_1 : Monoid G]   [inst_2 : AddCom
mMonoid V] [inst_3 :…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma ext {φ ψ : Equiv ρ σ} (h : (φ : V → W) = ψ) : φ = ψ := by
  cases φ; cases ψ
  simpa using h

variable (ρ) in
/-- Any representation is equivalent to itself. -/
/-
**Representation.Equiv.refl** 是 Mathlib 中的一个定义，位于命名空间 `Representation.Equiv`。
形式化陈述：refl : Equiv ρ ρ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any representation is equivalent to itself.
-/
def refl : Equiv ρ ρ where
  __ := LinearEquiv.refl _ _
  isIntertwining' g := by simp
/-
**Representation.Equiv.toIntertwiningMap_refl** 是 Mathlib 中的一个定理，位于命名空间 `Represe
ntation.Equiv`。
形式化陈述：∀ {A : Type u_1} {G : Type u_2} {V : Type u_3} [inst : Semiring A] [inst_1
 : Monoid G] [inst_2 : AddCommMonoid V]   [inst_3 : _root_.Module A V] {ρ : Repr
esentation A G V},   ↑(Representation.Equiv.refl ρ) = Representation.Intertwinin
gMap.id ρ
参数：Representation.Equiv.refl ρ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toIntertwiningMap_refl : (refl ρ).toIntertwiningMap = .id ρ := rfl
/-
**Representation.Equiv.toLinearMap_refl** 是 Mathlib 中的一个定理，位于命名空间 `Representatio
n.Equiv`。
形式化陈述：∀ {A : Type u_1} {G : Type u_2} {V : Type u_3} [inst : Semiring A] [inst_1
 : Monoid G] [inst_2 : AddCommMonoid V]   [inst_3 : _root_.Module A V] {ρ : Repr
esentation A G V}, (↑(Representation.Equiv.refl ρ)).toLinearMap = LinearMap.id
参数：↑(Representation.Equiv.refl ρ)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toLinearMap_refl : (refl ρ).toLinearMap = LinearMap.id := rfl
/-
**Representation.Equiv.refl_apply** 是 Mathlib 中的一个定理，位于命名空间 `Representation.Equi
v`。
形式化陈述：∀ {A : Type u_1} {G : Type u_2} {V : Type u_3} [inst : Semiring A] [inst_1
 : Monoid G] [inst_2 : AddCommMonoid V]   [inst_3 : _root_.Module A V] {ρ : Repr
esentation A G V} (v : V), (Representation.Equiv.refl ρ) v = v
参数：v : V；Representation.Equiv.refl ρ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma refl_apply (v : V) : refl ρ v = v := rfl
/-
**Representation.Equiv.coe_toIntertwiningMap** 是 Mathlib 中的一个定理，位于命名空间 `Represen
tation.Equiv`。
形式化陈述：∀ {A : Type u_1} {G : Type u_2} {V : Type u_3} {W : Type u_4} [inst : Semi
ring A] [inst_1 : Monoid G]   [inst_2 : AddCommMonoid V] [inst_3 : AddCommMonoid
 W] [inst_4 : _root_.Module A V] [inst_5 : _root_.Module A W]   {ρ : Representat
ion A G V} {σ : Representation A G W} (φ : ρ.Equiv σ), ⇑↑φ = ⇑φ
参数：φ : ρ.Equiv σ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_toIntertwiningMap : ⇑φ.toIntertwiningMap = φ := rfl
/-
**Representation.Equiv.coe_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `Representation
.Equiv`。
形式化陈述：∀ {A : Type u_1} {G : Type u_2} {V : Type u_3} {W : Type u_4} [inst : Semi
ring A] [inst_1 : Monoid G]   [inst_2 : AddCommMonoid V] [inst_3 : AddCommMonoid
 W] [inst_4 : _root_.Module A V] [inst_5 : _root_.Module A W]   {ρ : Representat
ion A G V} {σ : Representation A G W} (φ : ρ.Equiv σ), ⇑(↑φ).toLinearMap = ⇑φ
参数：φ : ρ.Equiv σ；↑φ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_toLinearMap : ⇑φ.toLinearMap = φ := rfl
/-
**Representation.Equiv.coe_invFun** 是 Mathlib 中的一个引理，位于命名空间 `Representation.Equi
v`。
形式化陈述：coe_invFun : φ.invFun = φ.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_invFun : φ.invFun = φ.symm := rfl
/-
**Representation.Equiv.toLinearEquiv_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `Repr
esentation.Equiv`。
形式化陈述：toLinearEquiv_toLinearMap : φ.toLinearEquiv.toLinearMap = φ.toIntertwining
Map.toLinearMap
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearEquiv_toLinearMap :
  φ.toLinearEquiv.toLinearMap = φ.toIntertwiningMap.toLinearMap := rfl
/-
**Representation.Equiv.toLinearEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Representa
tion.Equiv`。
形式化陈述：toLinearEquiv_apply (v : V) : φ.toLinearEquiv v = φ.toIntertwiningMap v
参数：v : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearEquiv_apply (v : V) : φ.toLinearEquiv v = φ.toIntertwiningMap v := rfl

open LinearMap in
/-- The equiv between representations are symmetric. -/
@[symm]
/-
**Representation.Equiv.symm** 是 Mathlib 中的一个定义，位于命名空间 `Representation.Equiv`。
形式化陈述：symm (φ : Equiv ρ σ) : Equiv σ ρ where __
参数：φ : Equiv ρ σ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equiv between representations are symmetric.
-/
def symm (φ : Equiv ρ σ) : Equiv σ ρ where
  __ := φ.toLinearEquiv.symm
  isIntertwining' g := by
    rw [← cancel_left φ.toLinearEquiv.injective, ← comp_assoc, ← comp_assoc, φ.1.2 g, φ.comp_symm,
      comp_assoc, φ.comp_symm, id_comp, comp_id]

open LinearMap in
/-
**Representation.Equiv._root_.LinearEquiv.isIntertwining_symm_isIntertwining** 是
 Mathlib 中的一个引理，位于命名空间 `Representation.Equiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.LinearEquiv.isIntertwining_symm_isIntertwining {e : V ≃ₗ[A] W}
    (he : ∀ g, e ∘ₗ (ρ g) = (σ g) ∘ₗ e) (g : G) :
    e.symm ∘ₗ (σ g) = (ρ g) ∘ₗ e.symm := by
  apply e.comp_toLinearMap_eq_iff _ _ |>.1
  rw [← comp_assoc, ← comp_assoc, he g, e.comp_symm, id_comp, comp_assoc, e.comp_symm, comp_id]

@[simp]
/-
**Representation.Equiv.mk_symm** 是 Mathlib 中的一个引理，位于命名空间 `Representation.Equiv`。
形式化陈述：mk_symm {e : V ≃ₗ[A] W} (he : forall g, e ∘ₗ (ρ g) = (σ g) ∘ₗ e) : (mk e h
e).symm = mk e.symm (e.isIntertwining_symm_isIntertwining he)
参数：he : forall g, e ∘ₗ (ρ g) = (σ g) ∘ₗ e。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk_symm {e : V ≃ₗ[A] W} (he : ∀ g, e ∘ₗ (ρ g) = (σ g) ∘ₗ e) :
    (mk e he).symm = mk e.symm (e.isIntertwining_symm_isIntertwining he) := rfl
/-
**Representation.Equiv.toLinearMap_symm** 是 Mathlib 中的一个引理，位于命名空间 `Representatio
n.Equiv`。
形式化陈述：toLinearMap_symm (φ : Equiv ρ σ) : (symm φ).toLinearMap = φ.toLinearEquiv.
symm
参数：φ : Equiv ρ σ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toLinearMap_symm (φ : Equiv ρ σ) : (symm φ).toLinearMap = φ.toLinearEquiv.symm := rfl
/-
**Representation.Equiv.coe_symm** 是 Mathlib 中的一个引理，位于命名空间 `Representation.Equiv`
。
形式化陈述：coe_symm (φ : Equiv ρ σ) : ⇑φ.toLinearEquiv.symm = φ.symm
参数：φ : Equiv ρ σ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_symm (φ : Equiv ρ σ) : ⇑φ.toLinearEquiv.symm = φ.symm := rfl

variable {τ}

open LinearMap in
/-- Composition of two `Equiv`. -/
@[trans]
/-
**Representation.Equiv.trans** 是 Mathlib 中的一个定义，位于命名空间 `Representation.Equiv`。
形式化陈述：trans (φ : Equiv ρ σ) (ψ : Equiv σ τ) : Equiv ρ τ where __
参数：φ : Equiv ρ σ；ψ : Equiv σ τ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of two `Equiv`.
-/
def trans (φ : Equiv ρ σ) (ψ : Equiv σ τ) : Equiv ρ τ where
  __ := φ.toLinearEquiv.trans ψ.toLinearEquiv
  isIntertwining' g := by
    rw [LinearEquiv.coe_trans, comp_assoc, φ.1.2, ← comp_assoc, ψ.1.2, comp_assoc]

@[simp]
/-
**Representation.Equiv.toIntertwiningMap_trans** 是 Mathlib 中的一个引理，位于命名空间 `Repres
entation.Equiv`。
形式化陈述：toIntertwiningMap_trans (φ : Equiv ρ σ) (ψ : Equiv σ τ) : (φ.trans ψ).toIn
tertwiningMap = ψ.toIntertwiningMap.comp φ.toIntertwiningMap
参数：φ : Equiv ρ σ；ψ : Equiv σ τ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toIntertwiningMap_trans (φ : Equiv ρ σ) (ψ : Equiv σ τ) :
    (φ.trans ψ).toIntertwiningMap = ψ.toIntertwiningMap.comp φ.toIntertwiningMap := rfl

@[simp]
/-
**Representation.Equiv.toLinearMap_trans** 是 Mathlib 中的一个引理，位于命名空间 `Representati
on.Equiv`。
形式化陈述：toLinearMap_trans (φ : Equiv ρ σ) (ψ : Equiv σ τ) : (trans φ ψ).toLinearMa
p = ψ.toLinearMap ∘ₗ φ.toLinearMap
参数：φ : Equiv ρ σ；ψ : Equiv σ τ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toLinearMap_trans (φ : Equiv ρ σ) (ψ : Equiv σ τ) :
    (trans φ ψ).toLinearMap = ψ.toLinearMap ∘ₗ φ.toLinearMap := rfl

@[simp]
/-
**Representation.Equiv.trans_apply** 是 Mathlib 中的一个引理，位于命名空间 `Representation.Equ
iv`。
形式化陈述：trans_apply (φ : Equiv ρ σ) (ψ : Equiv σ τ) (v : V) : trans φ ψ v = ψ (φ v
)
参数：φ : Equiv ρ σ；ψ : Equiv σ τ；v : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma trans_apply (φ : Equiv ρ σ) (ψ : Equiv σ τ) (v : V) :
    trans φ ψ v = ψ (φ v) := rfl

@[simp]
/-
**Representation.Equiv.apply_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `Representatio
n.Equiv`。
形式化陈述：apply_symm_apply (φ : Equiv ρ σ) (v : W) : φ (φ.symm v) = v
参数：φ : Equiv ρ σ；v : W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Representation.Equiv.right_inv`：∀ {A : Type u_1} {G : Type u_2} {V : Typ
e u_3} {W : Type u_4} [inst : Semiring A] [inst_1 : Monoid G]   [inst_2 : AddCom
mMonoid V] [inst_3 :…
-/
lemma apply_symm_apply (φ : Equiv ρ σ) (v : W) : φ (φ.symm v) = v := φ.right_inv v

@[simp]
/-
**Representation.Equiv.symm_apply_apply** 是 Mathlib 中的一个引理，位于命名空间 `Representatio
n.Equiv`。
形式化陈述：symm_apply_apply (φ : Equiv ρ σ) (v : V) : φ.symm (φ v) = v
参数：φ : Equiv ρ σ；v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Representation.Equiv.left_inv`：∀ {A : Type u_1} {G : Type u_2} {V : Type
 u_3} {W : Type u_4} [inst : Semiring A] [inst_1 : Monoid G]   [inst_2 : AddComm
Monoid V] [inst_3 :…
-/
lemma symm_apply_apply (φ : Equiv ρ σ) (v : V) : φ.symm (φ v) = v := φ.left_inv v

@[simp]
/-
**Representation.Equiv.trans_symm** 是 Mathlib 中的一个引理，位于命名空间 `Representation.Equi
v`。
形式化陈述：trans_symm (φ : Equiv ρ σ) : φ.trans φ.symm = .refl ρ
参数：φ : Equiv ρ σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Representation.Equiv.ext`：ext {φ ψ : Equiv ρ σ} (h : (φ : V -> W) = ψ) :
 φ = ψ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Representation.Equiv.symm_apply_apply`：symm_apply_apply (φ : Equiv ρ σ) 
(v : V) : φ.symm (φ v) = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma trans_symm (φ : Equiv ρ σ) : φ.trans φ.symm = .refl ρ := by ext; simp

@[simp]
/-
**Representation.Equiv.symm_trans** 是 Mathlib 中的一个引理，位于命名空间 `Representation.Equi
v`。
形式化陈述：symm_trans (φ : Equiv ρ σ) : φ.symm.trans φ = .refl σ
参数：φ : Equiv ρ σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Representation.Equiv.ext`：ext {φ ψ : Equiv ρ σ} (h : (φ : V -> W) = ψ) :
 φ = ψ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Representation.Equiv.apply_symm_apply`：apply_symm_apply (φ : Equiv ρ σ) 
(v : W) : φ (φ.symm v) = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma symm_trans (φ : Equiv ρ σ) : φ.symm.trans φ = .refl σ := by ext; simp

end Equiv

end Monoid

end non_comm

variable {A G V W U : Type*} [CommSemiring A] [Monoid G] [AddCommMonoid V] [AddCommMonoid W]
  [AddCommMonoid U] [Module A V] [Module A W] [Module A U] (ρ : Representation A G V)
  (σ : Representation A G W) (τ : Representation A G U) (f : V →ₗ[A] W)

variable {ρ σ} in
/-
**Representation.Equiv.conj_apply_self** 是 Mathlib 中的一个定理，位于命名空间 `Representation
.Equiv`。
形式化陈述：∀ {A : Type u_1} {G : Type u_2} {V : Type u_3} {W : Type u_4} [inst : Comm
Semiring A] [inst_1 : Monoid G]   [inst_2 : AddCommMonoid V] [inst_3 : AddCommMo
noid W] [inst_4 : _root_.Module A V] [inst_5 : _root_.Module A W]   {ρ : Represe
ntation A G V} {σ : Representation A G W} (g : G) (φ : ρ.Equiv σ), φ.toLinearEqu
iv.conj (ρ g) = σ g
参数：g : G；φ : ρ.Equiv σ；ρ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Representation.IntertwiningMap.isIntertwining'`：∀ {A : Type u_1} {G : Ty
pe u_2} {V : Type u_3} {W : Type u_4} [inst : Semiring A] [inst_1 : Monoid G]   
[inst_2 : AddCommMonoid V] [inst_3 :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Representation.Equiv.apply_symm_apply`：apply_symm_apply (φ : Equiv ρ σ) 
(v : W) : φ (φ.symm v) = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Equiv.conj_apply_self (g : G) (φ : Equiv ρ σ) : φ.conj (ρ g) = σ g := by
  ext w
  have := (congr($(φ.symm.toIntertwiningMap.2 g) w)).symm
  simp only [LinearMap.coe_comp, coe_toLinearMap, Function.comp_apply, LinearEquiv.conj_apply_apply,
    coe_symm, toLinearEquiv_apply, coe_toIntertwiningMap] at this ⊢
  simp [this]

section Monoid

namespace IntertwiningMap

/-
**Representation.IntertwiningMap.** 是 Mathlib 中的一个实例，位于命名空间 `Representation.Inte
rtwiningMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul A (IntertwiningMap ρ σ) :=
  ⟨fun a f ↦ ⟨a • f.toLinearMap, by simp [LinearMap.smul_comp, LinearMap.comp_smul, f.2]⟩⟩
/-
**Representation.IntertwiningMap.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `Representat
ion.IntertwiningMap`。
形式化陈述：∀ {A : Type u_1} {G : Type u_2} {V : Type u_3} {W : Type u_4} [inst : Comm
Semiring A] [inst_1 : Monoid G]   [inst_2 : AddCommMonoid V] [inst_3 : AddCommMo
noid W] [inst_4 : _root_.Module A V] [inst_5 : _root_.Module A W]   (ρ : Represe
ntation A G V) (σ : Representation A G W) (a : A) (f : ρ.IntertwiningMap σ), ⇑(a
 • f) = a • ⇑f
参数：ρ : Representation A G V；σ : Representation A G W；a : A；f : ρ.IntertwiningMap
 σ；a • f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_smul (a : A) (f : IntertwiningMap ρ σ) :
    ((a • f : IntertwiningMap ρ σ) : V → W) = a • f := rfl

@[simp]
/-
**Representation.IntertwiningMap.toLinearMap_smul** 是 Mathlib 中的一个引理，位于命名空间 `Rep
resentation.IntertwiningMap`。
形式化陈述：toLinearMap_smul (a : A) (f : IntertwiningMap ρ σ) : (a • f).toLinearMap =
 a • f.toLinearMap
参数：a : A；f : IntertwiningMap ρ σ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toLinearMap_smul (a : A) (f : IntertwiningMap ρ σ) :
    (a • f).toLinearMap = a • f.toLinearMap := rfl
/-
**Representation.IntertwiningMap.smul_apply** 是 Mathlib 中的一个引理，位于命名空间 `Represent
ation.IntertwiningMap`。
形式化陈述：smul_apply (a : A) (f : IntertwiningMap ρ σ) (v : V) : (a • f) v = a • f v
参数：a : A；f : IntertwiningMap ρ σ；v : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma smul_apply (a : A) (f : IntertwiningMap ρ σ) (v : V) :
    (a • f) v = a • f v := rfl
/-
**Representation.IntertwiningMap.** 是 Mathlib 中的一个实例，位于命名空间 `Representation.Inte
rtwiningMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module A (IntertwiningMap ρ σ) :=
  fast_instance%
  Function.Injective.module A (coeFnAddMonoidHom ρ σ) DFunLike.coe_injective (coe_smul ρ σ)

set_option backward.isDefEq.respectTransparency false in
/-- An intertwining map is the same thing as a linear map over the group ring. -/
/-
**Representation.IntertwiningMap.equivLinearMapAsModule** 是 Mathlib 中的一个定义，位于命名空
间 `Representation.IntertwiningMap`。
形式化陈述：equivLinearMapAsModule : IntertwiningMap ρ σ ≃ₗ[A] ρ.asModule ->ₗ[A[G]] σ.
asModule where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An intertwining map is the same thing as a linear map over the group ring.
-/
def equivLinearMapAsModule :
    IntertwiningMap ρ σ ≃ₗ[A] ρ.asModule →ₗ[A[G]] σ.asModule where
  toFun f :=
    { toFun := f.toLinearMap
      map_add' := f.toLinearMap.map_add'
      map_smul' m v := by
        induction m using MonoidAlgebra.induction_linear with
          | zero => simp [f.toLinearMap.map_zero]
          | add x y hx hy => simp [add_smul, map_add, hx, hy]
          | single g a => simp [f.isIntertwining]; rfl }
  invFun f :=
    { toLinearMap := { f with
        map_smul' a v := by simp }
      isIntertwining' g := by ext v; simpa using! f.map_smul' (MonoidAlgebra.single g 1) v }
  map_add' g₁ g₂ := by ext; simp
  map_smul' t g := by ext; simp
  left_inv f := rfl
  right_inv f := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Composition of intertwining maps. -/
/-
**Representation.IntertwiningMap.llcomp** 是 Mathlib 中的一个定义，位于命名空间 `Representatio
n.IntertwiningMap`。
形式化陈述：llcomp : IntertwiningMap σ τ ->ₗ[A] IntertwiningMap ρ σ ->ₗ[A] Intertwinin
gMap ρ τ where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of intertwining maps.
-/
def llcomp : IntertwiningMap σ τ →ₗ[A] IntertwiningMap ρ σ →ₗ[A] IntertwiningMap ρ τ where
  toFun f :=
    { toFun g := ((f.toLinearMap.comp g.toLinearMap).intertwiningMap_of_isIntertwiningMap ρ τ
      (by intro γ v; simp [f.isIntertwining, g.isIntertwining]))
      map_add' _ _ := by ext; simp [map_add, toLinearMap_apply]
      map_smul' _ _ := by ext; simp [toLinearMap_apply] }
  map_add' _ _ := by ext; simp [toLinearMap_apply]
  map_smul' _ _ := by ext; simp [toLinearMap_apply]
/-
**Representation.IntertwiningMap.comp_def** 是 Mathlib 中的一个引理，位于命名空间 `Representat
ion.IntertwiningMap`。
形式化陈述：comp_def (f : IntertwiningMap σ τ) (g : IntertwiningMap ρ σ) : comp f g = 
llcomp _ _ _ f g
参数：f : IntertwiningMap σ τ；g : IntertwiningMap ρ σ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_def (f : IntertwiningMap σ τ) (g : IntertwiningMap ρ σ) :
    comp f g = llcomp _ _ _ f g := rfl
/-
**Representation.IntertwiningMap.smul_comp** 是 Mathlib 中的一个引理，位于命名空间 `Representa
tion.IntertwiningMap`。
形式化陈述：smul_comp (a : A) (f : IntertwiningMap σ τ) (g : IntertwiningMap ρ σ) : (a
 • f).comp g = a • comp f g
参数：a : A；f : IntertwiningMap σ τ；g : IntertwiningMap ρ σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma smul_comp (a : A) (f : IntertwiningMap σ τ) (g : IntertwiningMap ρ σ) :
    (a • f).comp g = a • comp f g := by simp [comp_def]
/-
**Representation.IntertwiningMap.comp_smul** 是 Mathlib 中的一个引理，位于命名空间 `Representa
tion.IntertwiningMap`。
形式化陈述：comp_smul (a : A) (f : IntertwiningMap σ τ) (g : IntertwiningMap ρ σ) : co
mp f (a • g) = a • comp f g
参数：a : A；f : IntertwiningMap σ τ；g : IntertwiningMap ρ σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_smul (a : A) (f : IntertwiningMap σ τ) (g : IntertwiningMap ρ σ) :
    comp f (a • g) = a • comp f g := by simp [comp_def]
/-
**Representation.IntertwiningMap.** 是 Mathlib 中的一个实例，位于命名空间 `Representation.Inte
rtwiningMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul (IntertwiningMap ρ ρ) where
  mul := comp
/-
**Representation.IntertwiningMap.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `Representati
on.IntertwiningMap`。
形式化陈述：∀ {A : Type u_1} {G : Type u_2} {V : Type u_3} [inst : CommSemiring A] [in
st_1 : Monoid G] [inst_2 : AddCommMonoid V]   [inst_3 : _root_.Module A V] (ρ : 
Representation A G V) (f g : ρ.IntertwiningMap ρ),   (f * g).toLinearMap = f.toL
inearMap * g.toLinearMap
参数：ρ : Representation A G V；f g : ρ.IntertwiningMap ρ；f * g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_mul (f g : IntertwiningMap ρ ρ) :
    (f * g).toLinearMap = f.toLinearMap * g.toLinearMap := rfl
/-
**Representation.IntertwiningMap.mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `Representa
tion.IntertwiningMap`。
形式化陈述：∀ {A : Type u_1} {G : Type u_2} {V : Type u_3} [inst : CommSemiring A] [in
st_1 : Monoid G] [inst_2 : AddCommMonoid V]   [inst_3 : _root_.Module A V] (ρ : 
Representation A G V) (f g : ρ.IntertwiningMap ρ) (v : V), (f * g) v = f (g v)
参数：ρ : Representation A G V；f g : ρ.IntertwiningMap ρ；v : V；f * g；g v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mul_apply (f g : IntertwiningMap ρ ρ) (v : V) : (f * g) v = f (g v) := rfl
/-
**Representation.IntertwiningMap.** 是 Mathlib 中的一个实例，位于命名空间 `Representation.Inte
rtwiningMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (IntertwiningMap ρ ρ) := ⟨id ρ⟩
/-
**Representation.IntertwiningMap.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `Representati
on.IntertwiningMap`。
形式化陈述：∀ {A : Type u_1} {G : Type u_2} {V : Type u_3} [inst : CommSemiring A] [in
st_1 : Monoid G] [inst_2 : AddCommMonoid V]   [inst_3 : _root_.Module A V] (ρ : 
Representation A G V), ⇑1 = id
参数：ρ : Representation A G V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_one : ((1 : IntertwiningMap ρ ρ) : V → V) = (_root_.id : V → V) := rfl
/-
**Representation.IntertwiningMap.** 是 Mathlib 中的一个实例，位于命名空间 `Representation.Inte
rtwiningMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Semigroup (IntertwiningMap ρ ρ) :=
  Function.Injective.semigroup (fun f : IntertwiningMap ρ ρ => f.toLinearMap)
    (toLinearMap_injective ρ ρ) (coe_mul ρ)
/-
**Representation.IntertwiningMap.** 是 Mathlib 中的一个实例，位于命名空间 `Representation.Inte
rtwiningMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Pow (IntertwiningMap ρ ρ) ℕ := ⟨fun f n => npowRecAuto n f⟩
/-
**Representation.IntertwiningMap.** 是 Mathlib 中的一个实例，位于命名空间 `Representation.Inte
rtwiningMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Monoid (IntertwiningMap ρ ρ) :=
  Function.Injective.monoid (fun f : IntertwiningMap ρ ρ => f.toLinearMap)
    (toLinearMap_injective ρ ρ) rfl (fun _ _ => rfl)
    (fun f n => by
      induction n with
      | zero => rfl
      | succ n ih => simp only [pow_succ, coe_mul, show f ^ (n + 1) = f ^ n * f from rfl, ih])
/-
**Representation.IntertwiningMap.** 是 Mathlib 中的一个实例，位于命名空间 `Representation.Inte
rtwiningMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NatCast (IntertwiningMap ρ ρ) where
  natCast n := n • (1 : IntertwiningMap ρ ρ)
/-
**Representation.IntertwiningMap.instSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Represe
ntation.IntertwiningMap`。
形式化陈述：instSemiring : Semiring (IntertwiningMap ρ ρ)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemiring : Semiring (IntertwiningMap ρ ρ) :=
  fast_instance%
  Function.Injective.semiring (fun f : IntertwiningMap ρ ρ => f.toLinearMap)
    (toLinearMap_injective ρ ρ) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (by
      intro f n
      induction n with
      | zero => rfl
      | succ n ih => simp [ih, pow_succ])
    (fun _ => rfl)
/-
**Representation.IntertwiningMap.** 是 Mathlib 中的一个实例，位于命名空间 `Representation.Inte
rtwiningMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra A (IntertwiningMap ρ ρ) :=
  Algebra.ofModule (fun a f g => rfl) (fun a f g => by ext; simp)
/-
**Representation.IntertwiningMap.algebraMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `Rep
resentation.IntertwiningMap`。
形式化陈述：∀ {A : Type u_1} {G : Type u_2} {V : Type u_3} [inst : CommSemiring A] [in
st_1 : Monoid G] [inst_2 : AddCommMonoid V]   [inst_3 : _root_.Module A V] (ρ : 
Representation A G V) (a : A), (algebraMap A (ρ.IntertwiningMap ρ)) a = a • 1
参数：ρ : Representation A G V；a : A；algebraMap A (ρ.IntertwiningMap ρ)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma algebraMap_apply (a : A) : algebraMap A (IntertwiningMap ρ ρ) a = a • 1 := rfl

/-- Intertwining maps from `ρ` to itself are the same as `A[G]`-linear endomorphisms. -/
/-
**Representation.IntertwiningMap.equivAlgEnd** 是 Mathlib 中的一个定义，位于命名空间 `Represen
tation.IntertwiningMap`。
形式化陈述：equivAlgEnd : IntertwiningMap ρ ρ ≃ₐ[A] Module.End A[G] ρ.asModule
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Representation.instIsScalarTowerMonoidAlgebraAsModule`：∀ {k : Type u_1} 
{G : Type u_2} {V : Type u_3} [inst : CommSemiring k] [inst_1 : Monoid G] [inst_
2 : AddCommMonoid V]   [inst_3 : _root_.Mod…

--- 原说明 ---
Intertwining maps from `ρ` to itself are the same as `A[G]`-linear endomorphisms
.
-/
noncomputable def equivAlgEnd :
    IntertwiningMap ρ ρ ≃ₐ[A] Module.End A[G] ρ.asModule :=
  AlgEquiv.ofLinearEquiv
    (equivLinearMapAsModule ρ ρ)
    rfl
    (by intro f g; rfl)
/-
**Representation.IntertwiningMap.isIntertwiningMap_of_mem_center** 是 Mathlib 中的一
个定理，位于命名空间 `Representation.IntertwiningMap`。
形式化陈述：isIntertwiningMap_of_mem_center (g : G) (hg : g in Submonoid.center G) : I
sIntertwiningMap ρ ρ (ρ g)
参数：g : G；hg : g in Submonoid.center G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Representation.isIntertwiningMap_iff`：∀ {A : Type u_1} {G : Type u_2} {V
 : Type u_3} {W : Type u_4} [inst : Semiring A] [inst_1 : Monoid G]   [inst_2 : 
AddCommMonoid V] [inst_3 :…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.End.mul_apply`：mul_apply (f g : Module.End R M) (x : M) : (f * g)
 x = f (g x)
· 使用定理 `MonoidHom.map_mul`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N) (a b : M), f (a * b) = f a * f b
· 使用定理 `Submonoid.mem_center_iff`：mem_center_iff {z : M} : z in center M ↔ foral
l g, g * z = z * g
-/
theorem isIntertwiningMap_of_mem_center (g : G) (hg : g ∈ Submonoid.center G) :
    IsIntertwiningMap ρ ρ (ρ g) := by
  rw [isIntertwiningMap_iff]
  intro g' v
  rw [Submonoid.mem_center_iff] at hg
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← ρ.map_mul, ← hg g', ρ.map_mul]

/-- If `g` is a central element of a monoid `G`, then this is the action of `g`, considered as an
  intertwining map from any representation of `G` to itself. -/
/-
**Representation.IntertwiningMap.centralMul** 是 Mathlib 中的一个定义，位于命名空间 `Represent
ation.IntertwiningMap`。
形式化陈述：centralMul (g : G) (hg : g in Submonoid.center G) : IntertwiningMap ρ ρ wh
ere toLinearMap
参数：g : G；hg : g in Submonoid.center G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `g` is a central element of a monoid `G`, then this is the action of `g`, con
sidered as an
  intertwining map from any representation of `G` to itself.
-/
def centralMul (g : G) (hg : g ∈ Submonoid.center G) : IntertwiningMap ρ ρ where
  toLinearMap := ρ g
  isIntertwining' x := LinearMap.ext <| (isIntertwiningMap_of_mem_center ρ g hg).isIntertwining x

/-- If `z` is a central element of the monoid algebra `A[G]`, then this is the action of `z`,
  considered as an intertwining map from any representation of `G` to itself. -/
/-
**Representation.IntertwiningMap.centralAlgebraMul** 是 Mathlib 中的一个定义，位于命名空间 `Re
presentation.IntertwiningMap`。
形式化陈述：centralAlgebraMul {z : A[G]} (hz : z in Submonoid.center A[G]) : ρ.Intertw
iningMap ρ where toLinearMap
参数：hz : z in Submonoid.center A[G]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `z` is a central element of the monoid algebra `A[G]`, then this is the actio
n of `z`,
  considered as an intertwining map from any representation of `G` to itself.
-/
noncomputable def centralAlgebraMul {z : A[G]} (hz : z ∈ Submonoid.center A[G]) :
    ρ.IntertwiningMap ρ where
  toLinearMap := ρ.asAlgebraHom z
  isIntertwining' _ := by simp_rw [← ρ.asAlgebraHom_of, ← Module.End.mul_eq_comp,
    ← map_mul, Submonoid.mem_center_iff.1 hz]
/-
**Representation.IntertwiningMap.centralAlgebraMul_apply** 是 Mathlib 中的一个定理，位于命名
空间 `Representation.IntertwiningMap`。
形式化陈述：∀ {A : Type u_1} {G : Type u_2} {V : Type u_3} [inst : CommSemiring A] [in
st_1 : Monoid G] [inst_2 : AddCommMonoid V]   [inst_3 : _root_.Module A V] (ρ : 
Representation A G V) {z : MonoidAlgebra A G}   (hz : z ∈ Submonoid.center (Mono
idAlgebra A G)) (v : V),   (Representation.IntertwiningMap.centralAlgebraMul ρ h
z) v = (ρ.asAlgebraHom z) v
参数：ρ : Representation A G V；hz : z ∈ Submonoid.center (MonoidAlgebra A G)；v : V；
Representation.IntertwiningMap.centralAlgebraMul ρ hz；ρ.asAlgebraHom z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma centralAlgebraMul_apply {z : A[G]} (hz : z ∈ Submonoid.center A[G]) (v : V) :
    centralAlgebraMul ρ hz v = ρ.asAlgebraHom z v := rfl

/-- `centralAlgebraMul` as monoid homomorphism from the center of `A[G]` to intertwining map
  from any representation of `G` to itself. -/
/-
**Representation.IntertwiningMap.centralAlgebraMulHom** 是 Mathlib 中的一个定义，位于命名空间 
`Representation.IntertwiningMap`。
形式化陈述：{A : Type u_1} →   {G : Type u_2} →     {V : Type u_3} →       [inst : Com
mSemiring A] →         [inst_1 : Monoid G] →           [inst_2 : AddCommMonoid V
] →             [inst_3 : _root_.Module A V] →               (ρ : Representation
 A G V) → ↥(Submonoid.center (MonoidAlgebra A G)) →* ρ.IntertwiningMap ρ
参数：ρ : Representation A G V；Submonoid.center (MonoidAlgebra A G)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`centralAlgebraMul` as monoid homomorphism from the center of `A[G]` to intertwi
ning map
  from any representation of `G` to itself.
-/
@[simps] noncomputable def centralAlgebraMulHom : Submonoid.center A[G] →* ρ.IntertwiningMap ρ where
  toFun z := centralAlgebraMul _ z.2
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

/-- `IntertwiningMap.toLinearMap` as a linear map. -/
/-
**Representation.IntertwiningMap.toLinearMapl** 是 Mathlib 中的一个定义，位于命名空间 `Represe
ntation.IntertwiningMap`。
形式化陈述：{A : Type u_1} →   {G : Type u_2} →     {V : Type u_3} →       {W : Type u
_4} →         [inst : CommSemiring A] →           [inst_1 : Monoid G] →         
    [inst_2 : AddCommMonoid V] →               [inst_3 : AddCommMonoid W] →     
            [inst_4 : _root_.Module A V] →                   [inst_5 : _root_.Mo
dule A W] →                     (ρ : Representation A G V) → (σ : Representation
 A G W) → ρ.IntertwiningMap σ →ₗ[A] V →ₗ[A] W
参数：ρ : Representation A G V；σ : Representation A G W。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IntertwiningMap.toLinearMap` as a linear map.
-/
@[simps] def toLinearMapl : IntertwiningMap ρ σ →ₗ[A] V →ₗ[A] W where
  toFun := toLinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {A G V W : Type*} [CommRing A] [Monoid G] [AddCommGroup V] [AddCommGroup W]
  [Module A V] [Module A W] (ρ : Representation A G V) (σ : Representation A G W) in
/-
**Representation.IntertwiningMap.** 是 Mathlib 中的一个实例，位于命名空间 `Representation.Inte
rtwiningMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Module.Finite A V] [IsNoetherian A W] :
    Module.Finite A (IntertwiningMap ρ σ) :=
  .of_injective (toLinearMapl (ρ := ρ) (σ := σ)) (toLinearMap_injective ρ σ)

variable {ρ σ} in
/-- A bijective intertwining map is an equivalence of representations. -/
noncomputable
/-
**Representation.IntertwiningMap.ofBijective** 是 Mathlib 中的一个定义，位于命名空间 `Represen
tation.IntertwiningMap`。
形式化陈述：ofBijective (f : IntertwiningMap ρ σ) (hf : Function.Bijective f) : Equiv 
ρ σ where isIntertwining'
参数：f : IntertwiningMap ρ σ；hf : Function.Bijective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ofBijective (f : IntertwiningMap ρ σ) (hf : Function.Bijective f) :
    Equiv ρ σ where
  isIntertwining' := f.isIntertwining'
  toLinearEquiv := LinearEquiv.ofBijective f.toLinearMap hf

@[simp]
/-
**Representation.IntertwiningMap.coe_ofBijective** 是 Mathlib 中的一个定理，位于命名空间 `Repr
esentation.IntertwiningMap`。
形式化陈述：coe_ofBijective (f : IntertwiningMap ρ σ) (hf : Function.Bijective f) : ⇑(
f.ofBijective hf) = ⇑f
参数：f : IntertwiningMap ρ σ；hf : Function.Bijective f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ofBijective (f : IntertwiningMap ρ σ) (hf : Function.Bijective f) :
    ⇑(f.ofBijective hf) = ⇑f := rfl

variable {P : Type*} [AddCommMonoid P] [Module A P] {π : Representation A G P}

variable {ρ σ τ}

/-- The tensor product of intertwining maps induced from tensor product of linear maps. -/
/-
**Representation.IntertwiningMap.tensor** 是 Mathlib 中的一个定义，位于命名空间 `Representatio
n.IntertwiningMap`。
形式化陈述：tensor (f : IntertwiningMap ρ σ) (g : IntertwiningMap τ π) : (tprod ρ τ).I
ntertwiningMap (tprod σ π) where toLinearMap
参数：f : IntertwiningMap ρ σ；g : IntertwiningMap τ π。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tensor product of intertwining maps induced from tensor product of linear ma
ps.
-/
def tensor (f : IntertwiningMap ρ σ) (g : IntertwiningMap τ π) :
    (tprod ρ τ).IntertwiningMap (tprod σ π) where
  toLinearMap := TensorProduct.map f.toLinearMap g.toLinearMap
  isIntertwining' x := by
    rw [tprod_apply, ← TensorProduct.map_comp, f.2, g.2, TensorProduct.map_comp, tprod_apply]

@[simp]
/-
**Representation.IntertwiningMap.toLinearMap_tensor** 是 Mathlib 中的一个引理，位于命名空间 `R
epresentation.IntertwiningMap`。
形式化陈述：toLinearMap_tensor (f : IntertwiningMap ρ σ) (g : IntertwiningMap τ π) : (
f.tensor g).toLinearMap = TensorProduct.map f.toLinearMap g.toLinearMap
参数：f : IntertwiningMap ρ σ；g : IntertwiningMap τ π。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toLinearMap_tensor (f : IntertwiningMap ρ σ) (g : IntertwiningMap τ π) :
    (f.tensor g).toLinearMap = TensorProduct.map f.toLinearMap g.toLinearMap := rfl

@[simp]
/-
**Representation.IntertwiningMap.tensor_add_left** 是 Mathlib 中的一个引理，位于命名空间 `Repr
esentation.IntertwiningMap`。
形式化陈述：tensor_add_left (f₁ f₂ : IntertwiningMap ρ σ) (g : IntertwiningMap τ π) : 
(f₁ + f₂).tensor g = f₁.tensor g + f₂.tensor g
参数：f₁ f₂ : IntertwiningMap ρ σ；g : IntertwiningMap τ π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Representation.IntertwiningMap.ext`：ext {f g : IntertwiningMap ρ σ} (h :
 f.toLinearMap = g.toLinearMap) : f = g
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
· 使用定理 `TensorProduct.add_tmul`：add_tmul (m₁ m₂ : M) (n : N) : (m₁ + m₂) otimesₜ
 n = m₁ otimesₜ n + m₂ otimesₜ[R] n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma tensor_add_left (f₁ f₂ : IntertwiningMap ρ σ) (g : IntertwiningMap τ π) :
    (f₁ + f₂).tensor g = f₁.tensor g + f₂.tensor g := by ext; simp [TensorProduct.add_tmul]

@[simp]
/-
**Representation.IntertwiningMap.tensor_add_right** 是 Mathlib 中的一个引理，位于命名空间 `Rep
resentation.IntertwiningMap`。
形式化陈述：tensor_add_right (f : IntertwiningMap ρ σ) (g₁ g₂ : IntertwiningMap τ π) :
 f.tensor (g₁ + g₂) = f.tensor g₁ + f.tensor g₂
参数：f : IntertwiningMap ρ σ；g₁ g₂ : IntertwiningMap τ π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Representation.IntertwiningMap.ext`：ext {f g : IntertwiningMap ρ σ} (h :
 f.toLinearMap = g.toLinearMap) : f = g
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
· 使用定理 `TensorProduct.tmul_add`：tmul_add (m : M) (n₁ n₂ : N) : m otimesₜ (n₁ + n
₂) = m otimesₜ n₁ + m otimesₜ[R] n₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma tensor_add_right (f : IntertwiningMap ρ σ) (g₁ g₂ : IntertwiningMap τ π) :
    f.tensor (g₁ + g₂) = f.tensor g₁ + f.tensor g₂ := by ext; simp [TensorProduct.tmul_add]

@[simp]
/-
**Representation.IntertwiningMap.tensor_smul_left** 是 Mathlib 中的一个引理，位于命名空间 `Rep
resentation.IntertwiningMap`。
形式化陈述：tensor_smul_left (a : A) (f : IntertwiningMap ρ σ) (g : IntertwiningMap τ 
π) : (a • f).tensor g = a • (f.tensor g)
参数：a : A；f : IntertwiningMap ρ σ；g : IntertwiningMap τ π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Representation.IntertwiningMap.ext`：ext {f g : IntertwiningMap ρ σ} (h :
 f.toLinearMap = g.toLinearMap) : f = g
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
· 使用定理 `TensorProduct.smul_tmul`：smul_tmul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (m : M) (n : N) : (r • m) otimesₜ n = m otimesₜ[R] (r • n)
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
· 使用定理 `TensorProduct.tmul_smul`：tmul_smul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (x : M) (y : N) : x otimesₜ (r • y) = r • x otimesₜ[R] y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma tensor_smul_left (a : A) (f : IntertwiningMap ρ σ) (g : IntertwiningMap τ π) :
    (a • f).tensor g = a • (f.tensor g) := by ext; simp [TensorProduct.smul_tmul]

@[simp]
/-
**Representation.IntertwiningMap.tensor_smul_right** 是 Mathlib 中的一个引理，位于命名空间 `Re
presentation.IntertwiningMap`。
形式化陈述：tensor_smul_right (f : IntertwiningMap ρ σ) (a : A) (g : IntertwiningMap τ
 π) : f.tensor (a • g) = a • (f.tensor g)
参数：f : IntertwiningMap ρ σ；a : A；g : IntertwiningMap τ π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Representation.IntertwiningMap.ext`：ext {f g : IntertwiningMap ρ σ} (h :
 f.toLinearMap = g.toLinearMap) : f = g
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
· 使用定理 `TensorProduct.tmul_smul`：tmul_smul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (x : M) (y : N) : x otimesₜ (r • y) = r • x otimesₜ[R] y
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma tensor_smul_right (f : IntertwiningMap ρ σ) (a : A) (g : IntertwiningMap τ π) :
    f.tensor (a • g) = a • (f.tensor g) := by ext; simp [TensorProduct.tmul_smul]

@[simp]
/-
**Representation.IntertwiningMap.tensor_apply** 是 Mathlib 中的一个引理，位于命名空间 `Represe
ntation.IntertwiningMap`。
形式化陈述：tensor_apply (f : IntertwiningMap ρ σ) (g : IntertwiningMap τ π) (v : V) (
w : U) : f.tensor g (v otimesₜ w) = f v otimesₜ g w
参数：f : IntertwiningMap ρ σ；g : IntertwiningMap τ π；v : V；w : U。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensor_apply (f : IntertwiningMap ρ σ) (g : IntertwiningMap τ π) (v : V) (w : U) :
    f.tensor g (v ⊗ₜ w) = f v ⊗ₜ g w := rfl

variable (ρ) in
/-- The intertwining map induced from `f : σ → τ` to `ρ.tprod σ → ρ.tprod τ`. -/
/-
**Representation.IntertwiningMap.lTensor** 是 Mathlib 中的一个定义，位于命名空间 `Representati
on.IntertwiningMap`。
形式化陈述：lTensor (f : IntertwiningMap σ τ) : (tprod ρ σ).IntertwiningMap (tprod ρ τ
)
参数：f : IntertwiningMap σ τ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The intertwining map induced from `f : σ → τ` to `ρ.tprod σ → ρ.tprod τ`.
-/
def lTensor (f : IntertwiningMap σ τ) :
    (tprod ρ σ).IntertwiningMap (tprod ρ τ) := tensor (id ρ) f

@[simp]
/-
**Representation.IntertwiningMap.toLinearMap_lTensor** 是 Mathlib 中的一个引理，位于命名空间 `
Representation.IntertwiningMap`。
形式化陈述：toLinearMap_lTensor (f : IntertwiningMap ρ σ) : (f.lTensor τ).toLinearMap 
= f.toLinearMap.lTensor U
参数：f : IntertwiningMap ρ σ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toLinearMap_lTensor (f : IntertwiningMap ρ σ) :
    (f.lTensor τ).toLinearMap = f.toLinearMap.lTensor U := rfl

@[simp]
/-
**Representation.IntertwiningMap.lTensor_apply** 是 Mathlib 中的一个引理，位于命名空间 `Repres
entation.IntertwiningMap`。
形式化陈述：lTensor_apply (f : IntertwiningMap σ τ) (v : V) (w : W) : f.lTensor ρ (v o
timesₜ w) = v otimesₜ f w
参数：f : IntertwiningMap σ τ；v : V；w : W。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lTensor_apply (f : IntertwiningMap σ τ) (v : V) (w : W) :
    f.lTensor ρ (v ⊗ₜ w) = v ⊗ₜ f w := rfl

@[simp]
/-
**Representation.IntertwiningMap.lTensor_id** 是 Mathlib 中的一个引理，位于命名空间 `Represent
ation.IntertwiningMap`。
形式化陈述：lTensor_id : lTensor ρ (id σ) = id (tprod ρ σ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Representation.IntertwiningMap.ext`：ext {f g : IntertwiningMap ρ σ} (h :
 f.toLinearMap = g.toLinearMap) : f = g
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
· 使用定理 `LinearMap.lTensor_id`：lTensor_id : (id : N ->ₗ[R] N).lTensor M = id
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lTensor_id : lTensor ρ (id σ) = id (tprod ρ σ) := by ext; simp

@[simp]
/-
**Representation.IntertwiningMap.lTensor_zero** 是 Mathlib 中的一个引理，位于命名空间 `Represe
ntation.IntertwiningMap`。
形式化陈述：lTensor_zero : lTensor ρ (0 : IntertwiningMap σ τ) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Representation.IntertwiningMap.ext`：ext {f g : IntertwiningMap ρ σ} (h :
 f.toLinearMap = g.toLinearMap) : f = g
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
· 使用定理 `LinearMap.lTensor_zero`：lTensor_zero : lTensor M (0 : N ->ₗ[R] P) = 0
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lTensor_zero : lTensor ρ (0 : IntertwiningMap σ τ) = 0 := by ext; simp

@[simp]
/-
**Representation.IntertwiningMap.lTensor_add** 是 Mathlib 中的一个引理，位于命名空间 `Represen
tation.IntertwiningMap`。
形式化陈述：lTensor_add (f₁ f₂ : IntertwiningMap σ τ) : lTensor ρ (f₁ + f₂) = lTensor 
ρ f₁ + lTensor ρ f₂
参数：f₁ f₂ : IntertwiningMap σ τ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Representation.IntertwiningMap.tensor_add_right`：tensor_add_right (f : I
ntertwiningMap ρ σ) (g₁ g₂ : IntertwiningMap τ π) : f.tensor (g₁ + g₂) = f.tenso
r g₁ + f.tensor g₂
-/
lemma lTensor_add (f₁ f₂ : IntertwiningMap σ τ) :
    lTensor ρ (f₁ + f₂) = lTensor ρ f₁ + lTensor ρ f₂ := tensor_add_right _ _ _

@[simp]
/-
**Representation.IntertwiningMap.lTensor_smul** 是 Mathlib 中的一个引理，位于命名空间 `Represe
ntation.IntertwiningMap`。
形式化陈述：lTensor_smul (a : A) (f : IntertwiningMap σ τ) : lTensor ρ (a • f) = a • l
Tensor ρ f
参数：a : A；f : IntertwiningMap σ τ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Representation.IntertwiningMap.tensor_smul_right`：tensor_smul_right (f :
 IntertwiningMap ρ σ) (a : A) (g : IntertwiningMap τ π) : f.tensor (a • g) = a •
 (f.tensor g)
-/
lemma lTensor_smul (a : A) (f : IntertwiningMap σ τ) :
    lTensor ρ (a • f) = a • lTensor ρ f := tensor_smul_right _ _ _

variable (ρ) in
/-- The natural intertwining map `σ.tprod ρ → τ.tprod ρ` induced by `f : σ → τ`. -/
/-
**Representation.IntertwiningMap.rTensor** 是 Mathlib 中的一个定义，位于命名空间 `Representati
on.IntertwiningMap`。
形式化陈述：rTensor (f : IntertwiningMap σ τ) : (tprod σ ρ).IntertwiningMap (tprod τ ρ
)
参数：f : IntertwiningMap σ τ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural intertwining map `σ.tprod ρ → τ.tprod ρ` induced by `f : σ → τ`.
-/
def rTensor (f : IntertwiningMap σ τ) :
    (tprod σ ρ).IntertwiningMap (tprod τ ρ) := tensor f (id ρ)

@[simp]
/-
**Representation.IntertwiningMap.toLinearMap_rTensor** 是 Mathlib 中的一个引理，位于命名空间 `
Representation.IntertwiningMap`。
形式化陈述：toLinearMap_rTensor (f : IntertwiningMap σ τ) : (f.rTensor ρ).toLinearMap 
= f.toLinearMap.rTensor V
参数：f : IntertwiningMap σ τ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toLinearMap_rTensor (f : IntertwiningMap σ τ) :
    (f.rTensor ρ).toLinearMap = f.toLinearMap.rTensor V := rfl

@[simp]
/-
**Representation.IntertwiningMap.rTensor_apply** 是 Mathlib 中的一个引理，位于命名空间 `Repres
entation.IntertwiningMap`。
形式化陈述：rTensor_apply (f : IntertwiningMap σ τ) (v : V) (w : W) : f.rTensor ρ (w o
timesₜ v) = f w otimesₜ v
参数：f : IntertwiningMap σ τ；v : V；w : W。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma rTensor_apply (f : IntertwiningMap σ τ) (v : V) (w : W) :
    f.rTensor ρ (w ⊗ₜ v) = f w ⊗ₜ v := rfl

@[simp]
/-
**Representation.IntertwiningMap.rTensor_id** 是 Mathlib 中的一个引理，位于命名空间 `Represent
ation.IntertwiningMap`。
形式化陈述：rTensor_id : rTensor ρ (id σ) = id (tprod σ ρ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Representation.IntertwiningMap.ext`：ext {f g : IntertwiningMap ρ σ} (h :
 f.toLinearMap = g.toLinearMap) : f = g
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
· 使用定理 `LinearMap.rTensor_id`：rTensor_id : (id : N ->ₗ[R] N).rTensor M = id
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rTensor_id : rTensor ρ (id σ) = id (tprod σ ρ) := by ext; simp

@[simp]
/-
**Representation.IntertwiningMap.rTensor_zero** 是 Mathlib 中的一个引理，位于命名空间 `Represe
ntation.IntertwiningMap`。
形式化陈述：rTensor_zero : rTensor ρ (0 : IntertwiningMap σ τ) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Representation.IntertwiningMap.ext`：ext {f g : IntertwiningMap ρ σ} (h :
 f.toLinearMap = g.toLinearMap) : f = g
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
· 使用定理 `LinearMap.rTensor_zero`：rTensor_zero : rTensor M (0 : N ->ₗ[R] P) = 0
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rTensor_zero : rTensor ρ (0 : IntertwiningMap σ τ) = 0 := by ext; simp

@[simp]
/-
**Representation.IntertwiningMap.rTensor_add** 是 Mathlib 中的一个引理，位于命名空间 `Represen
tation.IntertwiningMap`。
形式化陈述：rTensor_add (f₁ f₂ : IntertwiningMap σ τ) : rTensor ρ (f₁ + f₂) = rTensor 
ρ f₁ + rTensor ρ f₂
参数：f₁ f₂ : IntertwiningMap σ τ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Representation.IntertwiningMap.tensor_add_left`：tensor_add_left (f₁ f₂ :
 IntertwiningMap ρ σ) (g : IntertwiningMap τ π) : (f₁ + f₂).tensor g = f₁.tensor
 g + f₂.tensor g
-/
lemma rTensor_add (f₁ f₂ : IntertwiningMap σ τ) :
    rTensor ρ (f₁ + f₂) = rTensor ρ f₁ + rTensor ρ f₂ := tensor_add_left _ _ _

@[simp]
/-
**Representation.IntertwiningMap.rTensor_smul** 是 Mathlib 中的一个引理，位于命名空间 `Represe
ntation.IntertwiningMap`。
形式化陈述：rTensor_smul (a : A) (f : IntertwiningMap σ τ) : rTensor ρ (a • f) = a • r
Tensor ρ f
参数：a : A；f : IntertwiningMap σ τ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Representation.IntertwiningMap.tensor_smul_left`：tensor_smul_left (a : A
) (f : IntertwiningMap ρ σ) (g : IntertwiningMap τ π) : (a • f).tensor g = a • (
f.tensor g)
-/
lemma rTensor_smul (a : A) (f : IntertwiningMap σ τ) :
    rTensor ρ (a • f) = a • rTensor ρ f := tensor_smul_left _ _ _

variable {Q : Type*} [AddCommMonoid Q] [Module A Q] {υ : Representation A G Q}
/-
**Representation.IntertwiningMap.rTensor_comp_lTensor** 是 Mathlib 中的一个引理，位于命名空间 
`Representation.IntertwiningMap`。
形式化陈述：rTensor_comp_lTensor (f : ρ.IntertwiningMap τ) (g : σ.IntertwiningMap υ) :
 (f.rTensor υ).comp (g.lTensor ρ) = f.tensor g
参数：f : ρ.IntertwiningMap τ；g : σ.IntertwiningMap υ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Representation.IntertwiningMap.ext`：ext {f g : IntertwiningMap ρ σ} (h :
 f.toLinearMap = g.toLinearMap) : f = g
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
· 使用定理 `LinearMap.rTensor_comp_lTensor`：rTensor_comp_lTensor (f : M ->ₗ[R] P) (g
 : N ->ₗ[R] Q) : (f.rTensor Q).comp (g.lTensor M) = map f g
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rTensor_comp_lTensor (f : ρ.IntertwiningMap τ) (g : σ.IntertwiningMap υ) :
    (f.rTensor υ).comp (g.lTensor ρ) = f.tensor g := by ext; simp
/-
**Representation.IntertwiningMap.lTensor_comp_rTensor** 是 Mathlib 中的一个引理，位于命名空间 
`Representation.IntertwiningMap`。
形式化陈述：lTensor_comp_rTensor (f : ρ.IntertwiningMap τ) (g : σ.IntertwiningMap υ) :
 (g.lTensor τ).comp (f.rTensor σ) = f.tensor g
参数：f : ρ.IntertwiningMap τ；g : σ.IntertwiningMap υ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Representation.IntertwiningMap.ext`：ext {f g : IntertwiningMap ρ σ} (h :
 f.toLinearMap = g.toLinearMap) : f = g
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
· 使用定理 `LinearMap.lTensor_comp_rTensor`：lTensor_comp_rTensor (f : M ->ₗ[R] P) (g
 : N ->ₗ[R] Q) : (g.lTensor P).comp (f.rTensor N) = map f g
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lTensor_comp_rTensor (f : ρ.IntertwiningMap τ) (g : σ.IntertwiningMap υ) :
    (g.lTensor τ).comp (f.rTensor σ) = f.tensor g := by ext; simp

end IntertwiningMap

namespace TensorProduct

noncomputable section

/-- Equivalence between representations induced from `TensorProduct.comm`. -/
/-
**Representation.TensorProduct.comm** 是 Mathlib 中的一个定义，位于命名空间 `Representation.Te
nsorProduct`。
形式化陈述：comm : (tprod ρ σ).Equiv (tprod σ ρ)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence between representations induced from `TensorProduct.comm`.
-/
def comm : (tprod ρ σ).Equiv (tprod σ ρ) :=
  .mk (_root_.TensorProduct.comm A V W) <| fun g ↦ by ext; simp

@[simp]
/-
**Representation.TensorProduct.toLinearMap_comm** 是 Mathlib 中的一个引理，位于命名空间 `Repre
sentation.TensorProduct`。
形式化陈述：toLinearMap_comm : (comm ρ σ).toLinearMap = _root_.TensorProduct.comm A V 
W
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toLinearMap_comm : (comm ρ σ).toLinearMap = _root_.TensorProduct.comm A V W := rfl

@[simp]
/-
**Representation.TensorProduct.comm_apply** 是 Mathlib 中的一个引理，位于命名空间 `Representat
ion.TensorProduct`。
形式化陈述：comm_apply (v : V) (w : W) : comm ρ σ (v otimesₜ w) = w otimesₜ v
参数：v : V；w : W。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comm_apply (v : V) (w : W) : comm ρ σ (v ⊗ₜ w) = w ⊗ₜ v := rfl
/-
**Representation.TensorProduct.comm_comp_lTensor** 是 Mathlib 中的一个引理，位于命名空间 `Repr
esentation.TensorProduct`。
形式化陈述：comm_comp_lTensor (f : IntertwiningMap σ τ) : (comm ρ τ).comp (f.lTensor ρ
) = (f.rTensor ρ).comp (comm ρ σ).toIntertwiningMap
参数：f : IntertwiningMap σ τ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Representation.IntertwiningMap.ext`：ext {f g : IntertwiningMap ρ σ} (h :
 f.toLinearMap = g.toLinearMap) : f = g
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
lemma comm_comp_lTensor (f : IntertwiningMap σ τ) :
    (comm ρ τ).comp (f.lTensor ρ) = (f.rTensor ρ).comp (comm ρ σ).toIntertwiningMap := by ext; simp
/-
**Representation.TensorProduct.comm_comp_rTensor** 是 Mathlib 中的一个引理，位于命名空间 `Repr
esentation.TensorProduct`。
形式化陈述：comm_comp_rTensor (f : IntertwiningMap σ τ) : (comm τ ρ).comp (f.rTensor ρ
) = (f.lTensor ρ).comp (comm σ ρ).toIntertwiningMap
参数：f : IntertwiningMap σ τ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Representation.IntertwiningMap.ext`：ext {f g : IntertwiningMap ρ σ} (h :
 f.toLinearMap = g.toLinearMap) : f = g
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
lemma comm_comp_rTensor (f : IntertwiningMap σ τ) :
    (comm τ ρ).comp (f.rTensor ρ) = (f.lTensor ρ).comp (comm σ ρ).toIntertwiningMap := by ext; simp
/-
**Representation.TensorProduct.comm_symm** 是 Mathlib 中的一个引理，位于命名空间 `Representati
on.TensorProduct`。
形式化陈述：comm_symm : (comm σ ρ).symm = comm ρ σ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comm_symm : (comm σ ρ).symm = comm ρ σ := by rfl

/-- The `Equiv` between representations induced from `TensorProduct.assoc`. -/
/-
**Representation.TensorProduct.assoc** 是 Mathlib 中的一个定义，位于命名空间 `Representation.T
ensorProduct`。
形式化陈述：assoc : (tprod (tprod ρ σ) τ).Equiv (tprod ρ (tprod σ τ))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Equiv` between representations induced from `TensorProduct.assoc`.
-/
def assoc : (tprod (tprod ρ σ) τ).Equiv (tprod ρ (tprod σ τ)) :=
  .mk (_root_.TensorProduct.assoc A V W U) <| fun g ↦ by ext; simp

@[simp]
/-
**Representation.TensorProduct.toLinearMap_assoc** 是 Mathlib 中的一个引理，位于命名空间 `Repr
esentation.TensorProduct`。
形式化陈述：toLinearMap_assoc : (assoc ρ σ τ).toLinearMap = _root_.TensorProduct.assoc
 A V W U
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toLinearMap_assoc : (assoc ρ σ τ).toLinearMap = _root_.TensorProduct.assoc A V W U := rfl

@[simp]
/-
**Representation.TensorProduct.assoc_symm_toLinearMap** 是 Mathlib 中的一个引理，位于命名空间 
`Representation.TensorProduct`。
形式化陈述：assoc_symm_toLinearMap : (assoc ρ σ τ).symm.toLinearMap = (_root_.TensorPr
oduct.assoc A V W U).symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma assoc_symm_toLinearMap : (assoc ρ σ τ).symm.toLinearMap =
  (_root_.TensorProduct.assoc A V W U).symm := rfl

@[simp]
/-
**Representation.TensorProduct.assoc_apply** 是 Mathlib 中的一个引理，位于命名空间 `Representa
tion.TensorProduct`。
形式化陈述：assoc_apply (v : V) (w : W) (u : U) : assoc ρ σ τ ((v otimesₜ w) otimesₜ u
) = v otimesₜ (w otimesₜ u)
参数：v : V；w : W；u : U。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma assoc_apply (v : V) (w : W) (u : U) : assoc ρ σ τ ((v ⊗ₜ w) ⊗ₜ u) = v ⊗ₜ (w ⊗ₜ u) := rfl

variable (A) in
/-- The `Equiv` between representations induced from `TensorProduct.rid`. -/
/-
**Representation.TensorProduct.rid** 是 Mathlib 中的一个定义，位于命名空间 `Representation.Ten
sorProduct`。
形式化陈述：rid : (σ.tprod (trivial A G A)).Equiv σ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Equiv` between representations induced from `TensorProduct.rid`.
-/
def rid : (σ.tprod (trivial A G A)).Equiv σ :=
  .mk (_root_.TensorProduct.rid A W) <| fun g ↦ by ext; simp

@[simp]
/-
**Representation.TensorProduct.toLinearMap_rid** 是 Mathlib 中的一个引理，位于命名空间 `Repres
entation.TensorProduct`。
形式化陈述：toLinearMap_rid : (rid A σ).toLinearMap = _root_.TensorProduct.rid A W
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toLinearMap_rid : (rid A σ).toLinearMap = _root_.TensorProduct.rid A W := rfl

@[simp]
/-
**Representation.TensorProduct.rid_apply** 是 Mathlib 中的一个引理，位于命名空间 `Representati
on.TensorProduct`。
形式化陈述：rid_apply (w : W) (a : A) : rid A σ (w otimesₜ a) = a • w
参数：w : W；a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma rid_apply (w : W) (a : A) : rid A σ (w ⊗ₜ a) = a • w := rfl

@[simp]
/-
**Representation.TensorProduct.rid_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `Represe
ntation.TensorProduct`。
形式化陈述：rid_symm_apply (w : W) : (rid A σ).symm w = w otimesₜ 1
参数：w : W。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma rid_symm_apply (w : W) : (rid A σ).symm w = w ⊗ₜ 1 := rfl

variable (A) in
/-- The `Equiv` between representations induced from `TensorProduct.lid`. -/
/-
**Representation.TensorProduct.lid** 是 Mathlib 中的一个定义，位于命名空间 `Representation.Ten
sorProduct`。
形式化陈述：lid : ((trivial A G A).tprod σ).Equiv σ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Equiv` between representations induced from `TensorProduct.lid`.
-/
def lid : ((trivial A G A).tprod σ).Equiv σ :=
  .mk (_root_.TensorProduct.lid A W) <| fun g ↦ by ext; simp

@[simp]
/-
**Representation.TensorProduct.toLinearMap_lid** 是 Mathlib 中的一个引理，位于命名空间 `Repres
entation.TensorProduct`。
形式化陈述：toLinearMap_lid : (lid A σ).toLinearMap = _root_.TensorProduct.lid A W
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toLinearMap_lid : (lid A σ).toLinearMap = _root_.TensorProduct.lid A W := rfl

@[simp]
/-
**Representation.TensorProduct.lid_apply** 是 Mathlib 中的一个引理，位于命名空间 `Representati
on.TensorProduct`。
形式化陈述：lid_apply (a : A) (w : W) : lid A σ (a otimesₜ w) = a • w
参数：a : A；w : W。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lid_apply (a : A) (w : W) : lid A σ (a ⊗ₜ w) = a • w := rfl

@[simp]
/-
**Representation.TensorProduct.lid_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `Represe
ntation.TensorProduct`。
形式化陈述：lid_symm_apply (w : W) : (lid A σ).symm w = 1 otimesₜ w
参数：w : W。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lid_symm_apply (w : W) : (lid A σ).symm w = 1 ⊗ₜ w := rfl

end

end TensorProduct

end Monoid

namespace Equiv

section Group

variable {G k V W : Type*} [Group G] [Field k] [AddCommGroup V] [Module k V] [AddCommGroup W]
    [Module k W] [FiniteDimensional k V] [FiniteDimensional k W]
    (ρ : Representation k G V) (σ : Representation k G W)

/-- dualTensorHom as an equivalence of representations. -/
/-
**Representation.Equiv.dualTensorHom** 是 Mathlib 中的一个定义，位于命名空间 `Representation.E
quiv`。
形式化陈述：{G : Type u_6} →   {k : Type u_7} →     {V : Type u_8} →       {W : Type u
_9} →         [inst : Group G] →           [inst_1 : Field k] →             [ins
t_2 : AddCommGroup V] →               [inst_3 : _root_.Module k V] →            
     [inst_4 : AddCommGroup W] →                   [inst_5 : _root_.Module k W] 
→                     [FiniteDimensional k V] →                       (ρ : Repre
sentation k G V) → (σ : Representation k G W) → (ρ.dual.tprod σ).Equiv (ρ.linHom
 σ)
参数：ρ : Representation k G V；σ : Representation k G W；ρ.dual.tprod σ；ρ.linHom σ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
dualTensorHom as an equivalence of representations.
-/
@[simps!] noncomputable def dualTensorHom : Equiv (tprod ρ.dual σ) (linHom ρ σ) where
  toLinearEquiv := dualTensorHomEquiv (R := k) (M := V) (N := W)
  isIntertwining' g := by
    ext v' w v; simp [Module.Dual.transpose_apply]

end Group

end Equiv

end Representation

