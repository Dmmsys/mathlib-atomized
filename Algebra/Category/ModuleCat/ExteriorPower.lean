/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# The exterior powers as functors on the category of modules

In this file, given `M : ModuleCat R` and `n : ℕ`, we define `M.exteriorPower n : ModuleCat R`,
and this extends to a functor `ModuleCat.exteriorPower.functor : ModuleCat R ⥤ ModuleCat R`.

-/

@[expose] public section

universe v u

open CategoryTheory

namespace ModuleCat

variable {R : Type u} [CommRing R]

/-- The exterior power of an object in `ModuleCat R`. -/
/-
**ModuleCat.exteriorPower** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：exteriorPower (M : ModuleCat.{v} R) (n : Nat) : ModuleCat.{max u v} R
参数：M : ModuleCat.{v} R；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The exterior power of an object in `ModuleCat R`.
-/
def exteriorPower (M : ModuleCat.{v} R) (n : ℕ) : ModuleCat.{max u v} R :=
  ModuleCat.of R (⋀[R]^n M)

-- this could be an abbrev, but using a def eases automation
/-- The type of `n`-alternating maps on `M : ModuleCat R` to `N : ModuleCat R`. -/
/-
**ModuleCat.AlternatingMap** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：AlternatingMap (M : ModuleCat.{v} R) (N : ModuleCat.{max u v} R) (n : Nat)
参数：M : ModuleCat.{v} R；N : ModuleCat.{max u v} R；n : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of `n`-alternating maps on `M : ModuleCat R` to `N : ModuleCat R`.
-/
def AlternatingMap (M : ModuleCat.{v} R) (N : ModuleCat.{max u v} R) (n : ℕ) :=
  _root_.AlternatingMap R M N (Fin n)
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (M : ModuleCat.{v} R) (N : ModuleCat.{max u v} R) (n : ℕ) :
    FunLike (M.AlternatingMap N n) (Fin n → M) N :=
  inferInstanceAs (FunLike (M [⋀^(Fin n)]→ₗ[R] N) (Fin n → M) N)

namespace AlternatingMap

variable {M : ModuleCat.{v} R} {N : ModuleCat.{max u v} R} {n : ℕ}

@[ext]
/-
**ModuleCat.AlternatingMap.ext** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat.AlternatingM
ap`。
形式化陈述：ext {φ φ' : M.AlternatingMap N n} (h : forall (x : Fin n -> M), φ x = φ' x
) : φ = φ'
参数：h : forall (x : Fin n -> M), φ x = φ' x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.ext`：ext {f f' : M [⋀^ι]->ₗ[R] N} (H : forall x, f x = f'
 x) : f = f'
-/
lemma ext {φ φ' : M.AlternatingMap N n} (h : ∀ (x : Fin n → M), φ x = φ' x) :
    φ = φ' :=
  _root_.AlternatingMap.ext h

variable (φ : M.AlternatingMap N n) {N' : ModuleCat.{max u v} R} (g : N ⟶ N')

/-- The postcomposition of an alternating map by a linear map. -/
/-
**ModuleCat.AlternatingMap.postcomp** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat.Alterna
tingMap`。
形式化陈述：postcomp : M.AlternatingMap N' n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The postcomposition of an alternating map by a linear map.
-/
def postcomp : M.AlternatingMap N' n :=
  g.hom.compAlternatingMap φ

@[simp]
/-
**ModuleCat.AlternatingMap.postcomp_apply** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat.A
lternatingMap`。
形式化陈述：postcomp_apply (x : Fin n -> M) : φ.postcomp g x = g (φ x)
参数：x : Fin n -> M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma postcomp_apply (x : Fin n → M) :
    φ.postcomp g x = g (φ x) := rfl

end AlternatingMap

namespace exteriorPower

/-- Constructor for elements in `M.exteriorPower n` when `M` is an object of `ModuleCat R`
and `n : ℕ`. -/
/-
**ModuleCat.exteriorPower.mk** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat.exteriorPower`
。
形式化陈述：mk {M : ModuleCat.{v} R} {n : Nat} : M.AlternatingMap (M.exteriorPower n) 
n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for elements in `M.exteriorPower n` when `M` is an object of `Module
Cat R`
and `n : ℕ`.
-/
def mk {M : ModuleCat.{v} R} {n : ℕ} :
    M.AlternatingMap (M.exteriorPower n) n :=
  exteriorPower.ιMulti _ _

@[ext]
/-
**ModuleCat.exteriorPower.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat.exteriorP
ower`。
形式化陈述：hom_ext {M : ModuleCat.{v} R} {N : ModuleCat.{max u v} R} {n : Nat} {f g :
 M.exteriorPower n ⟶ N} (h : mk.postcomp f = mk.postcomp g) : f = g
参数：h : mk.postcomp f = mk.postcomp g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ModuleCat.hom_ext`：hom_ext {M N : ModuleCat.{v} R} {f g : M ⟶ N} (hf : f
.hom = g.hom) : f = g
· 使用引理 `exteriorPower.linearMap_ext`：linearMap_ext {f : ⋀[R]^n M ->ₗ[R] N} {g : 
⋀[R]^n M ->ₗ[R] N} (heq : f.compAlternatingMap (ιMulti R n) = g.compAlternatingM
ap (ιMulti R n)) …
-/
lemma hom_ext {M : ModuleCat.{v} R} {N : ModuleCat.{max u v} R} {n : ℕ}
    {f g : M.exteriorPower n ⟶ N}
    (h : mk.postcomp f = mk.postcomp g) : f = g := by
  ext : 1
  exact exteriorPower.linearMap_ext h

/-- The morphism `M.exteriorPower n ⟶ N` induced by an alternating map. -/
/-
**ModuleCat.exteriorPower.desc** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat.exteriorPowe
r`。
形式化陈述：desc {M : ModuleCat.{v} R} {n : Nat} {N : ModuleCat.{max u v} R} (φ : M.Al
ternatingMap N n) : M.exteriorPower n ⟶ N
参数：φ : M.AlternatingMap N n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `M.exteriorPower n ⟶ N` induced by an alternating map.
-/
noncomputable def desc {M : ModuleCat.{v} R} {n : ℕ} {N : ModuleCat.{max u v} R}
    (φ : M.AlternatingMap N n) : M.exteriorPower n ⟶ N :=
  ofHom (exteriorPower.alternatingMapLinearEquiv φ)

@[simp]
/-
**ModuleCat.exteriorPower.desc_mk** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat.exteriorP
ower`。
形式化陈述：desc_mk {M : ModuleCat.{v} R} {n : Nat} {N : ModuleCat.{max u v} R} (φ : M
.AlternatingMap N n) (x : Fin n -> M) : desc φ (mk x) = φ x
参数：φ : M.AlternatingMap N n；x : Fin n -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `exteriorPower.alternatingMapLinearEquiv_apply_ιMulti`：alternatingMapLine
arEquiv_apply_ιMulti (f : M [⋀^Fin n]->ₗ[R] N) (a : Fin n -> M) : alternatingMap
LinearEquiv f (ιMulti R n a) = f a
-/
lemma desc_mk {M : ModuleCat.{v} R} {n : ℕ} {N : ModuleCat.{max u v} R}
    (φ : M.AlternatingMap N n) (x : Fin n → M) :
    desc φ (mk x) = φ x := by
  apply exteriorPower.alternatingMapLinearEquiv_apply_ιMulti

/-- The morphism `M.exteriorPower n ⟶ N.exteriorPower n` induced by a morphism `M ⟶ N`
in `ModuleCat R`. -/
/-
**ModuleCat.exteriorPower.map** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat.exteriorPower
`。
形式化陈述：map {M N : ModuleCat.{v} R} (f : M ⟶ N) (n : Nat) : M.exteriorPower n ⟶ N.
exteriorPower n
参数：f : M ⟶ N；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `M.exteriorPower n ⟶ N.exteriorPower n` induced by a morphism `M ⟶ 
N`
in `ModuleCat R`.
-/
noncomputable def map {M N : ModuleCat.{v} R} (f : M ⟶ N) (n : ℕ) :
    M.exteriorPower n ⟶ N.exteriorPower n :=
  ofHom (_root_.exteriorPower.map n f.hom)

@[simp]
/-
**ModuleCat.exteriorPower.map_mk** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat.exteriorPo
wer`。
形式化陈述：map_mk {M N : ModuleCat.{v} R} (f : M ⟶ N) {n : Nat} (x : Fin n -> M) : ma
p f n (mk x) = mk (f ∘ x)
参数：f : M ⟶ N；x : Fin n -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exteriorPower.map_apply_ιMulti`：map_apply_ιMulti (f : M ->ₗ[R] N) (m : F
in n -> M) : map n f (ιMulti R n m) = ιMulti R n (f ∘ m)
-/
lemma map_mk {M N : ModuleCat.{v} R} (f : M ⟶ N) {n : ℕ} (x : Fin n → M) :
    map f n (mk x) = mk (f ∘ x) := by
  apply exteriorPower.map_apply_ιMulti

variable (R) in
/-- The functor `ModuleCat R ⥤ ModuleCat R` which sends a module to its
`n`th exterior power. -/
@[simps]
/-
**ModuleCat.exteriorPower.functor** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat.exteriorP
ower`。
形式化陈述：functor (n : Nat) : ModuleCat.{v} R ⥤ ModuleCat.{max u v} R where obj M
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `ModuleCat R ⥤ ModuleCat R` which sends a module to its
`n`th exterior power.
-/
noncomputable def functor (n : ℕ) : ModuleCat.{v} R ⥤ ModuleCat.{max u v} R where
  obj M := M.exteriorPower n
  map f := map f n

/-- The isomorphism `M.exteriorPower 0 ≅ ModuleCat.of R R`. -/
/-
**ModuleCat.exteriorPower.iso** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat.exteriorPower
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `M.exteriorPower 0 ≅ ModuleCat.of R R`.
-/
noncomputable def iso₀ (M : ModuleCat.{u} R) : M.exteriorPower 0 ≅ ModuleCat.of R R :=
  (exteriorPower.zeroEquiv R M).toModuleIso

@[simp]
/-
**ModuleCat.exteriorPower.iso** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat.exteriorPower
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma iso₀_hom_apply {M : ModuleCat.{u} R} (f : Fin 0 → M) :
    (iso₀ M).hom (mk f) = 1 :=
  exteriorPower.zeroEquiv_ιMulti _

@[reassoc (attr := simp)]
/-
**ModuleCat.exteriorPower.iso** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat.exteriorPower
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma iso₀_hom_naturality {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    map f 0 ≫ (iso₀ N).hom = (iso₀ M).hom :=
  ModuleCat.hom_ext (exteriorPower.zeroEquiv_naturality f.hom)

/-- The isomorphism `M.exteriorPower 1 ≅ M`. -/
/-
**ModuleCat.exteriorPower.iso** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat.exteriorPower
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `M.exteriorPower 1 ≅ M`.
-/
noncomputable def iso₁ (M : ModuleCat.{u} R) : M.exteriorPower 1 ≅ M :=
  (exteriorPower.oneEquiv R M).toModuleIso

@[simp]
/-
**ModuleCat.exteriorPower.iso** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat.exteriorPower
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma iso₁_hom_apply {M : ModuleCat.{u} R} (f : Fin 1 → M) :
    (iso₁ M).hom (mk f) = f 0 :=
  exteriorPower.oneEquiv_ιMulti _

@[reassoc (attr := simp)]
/-
**ModuleCat.exteriorPower.iso** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat.exteriorPower
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma iso₁_hom_naturality {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    map f 1 ≫ (iso₁ N).hom = (iso₁ M).hom ≫ f :=
  ModuleCat.hom_ext (exteriorPower.oneEquiv_naturality f.hom)

variable (R)

set_option backward.defeqAttrib.useBackward true in
/-- The natural isomorphism `M.exteriorPower 0 ≅ ModuleCat.of R R`. -/
/-
**ModuleCat.exteriorPower.natIso** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat.exteriorPo
wer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism `M.exteriorPower 0 ≅ ModuleCat.of R R`.
-/
noncomputable def natIso₀ : functor.{u} R 0 ≅ (Functor.const _).obj (ModuleCat.of R R) :=
  NatIso.ofComponents iso₀

set_option backward.defeqAttrib.useBackward true in
/-- The natural isomorphism `M.exteriorPower 1 ≅ M`. -/
/-
**ModuleCat.exteriorPower.natIso** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat.exteriorPo
wer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism `M.exteriorPower 1 ≅ M`.
-/
noncomputable def natIso₁ : functor.{u} R 1 ≅ 𝟭 _ :=
  NatIso.ofComponents iso₁

end exteriorPower

end ModuleCat

