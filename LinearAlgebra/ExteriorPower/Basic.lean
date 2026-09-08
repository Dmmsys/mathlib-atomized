/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel, Joël Riou
-/
module

public import Mathlib.Algebra.Module.Presentation.Basic
public import Mathlib.LinearAlgebra.ExteriorAlgebra.OfAlternating

/-!
# Exterior powers

We study the exterior powers of a module `M` over a commutative ring `R`.

## Definitions

* `exteriorPower.ιMulti` is the canonical alternating map on `M` with values in `⋀[R]^n M`.

* `exteriorPower.presentation R n M` is the standard presentation of the `R`-module `⋀[R]^n M`.

* `exteriorPower.map n f : ⋀[R]^n M →ₗ[R] ⋀[R]^n N` is the linear map on `nth` exterior powers
  induced by a linear map `f : M →ₗ[R] N`. (See the file
  `Mathlib/Algebra/Category/ModuleCat/ExteriorPower.lean` for the corresponding functor
  `ModuleCat R ⥤ ModuleCat R`.)

## Theorems
* `exteriorPower.ιMulti_span`: The image of `exteriorPower.ιMulti` spans `⋀[R]^n M`.

* We construct `exteriorPower.alternatingMapLinearEquiv` which
  expresses the universal property of the exterior power as a
  linear equivalence `(M [⋀^Fin n]→ₗ[R] N) ≃ₗ[R] ⋀[R]^n M →ₗ[R] N` between
  alternating maps and linear maps from the exterior power.

-/

@[expose] public section

open scoped TensorProduct

universe u

variable (R : Type u) [CommRing R] (n : ℕ) {M N N' : Type*}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup N'] [Module R N']

namespace exteriorPower

open Function Set Set.powersetCard

/-! The canonical alternating map from `Fin n → M` to `⋀[R]^n M`. -/

/-- `exteriorAlgebra.ιMulti` is the alternating map from `Fin n → M` to `⋀[r]^n M`
induced by `exteriorAlgebra.ιMulti`, i.e. sending a family of vectors `m : Fin n → M` to the
product of its entries. -/
/-
**exteriorPower.** 是 Mathlib 中的一个定义，位于命名空间 `exteriorPower`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`exteriorAlgebra.ιMulti` is the alternating map from `Fin n → M` to `⋀[r]^n M`
induced by `exteriorAlgebra.ιMulti`, i.e. sending a family of vectors `m : Fin n
 → M` to the
product of its entries.
-/
def ιMulti : M [⋀^Fin n]→ₗ[R] (⋀[R]^n M) :=
  (ExteriorAlgebra.ιMulti R n).codRestrict (⋀[R]^n M) fun _ =>
    ExteriorAlgebra.ιMulti_range R n <| Set.mem_range_self _
/-
**exteriorPower.** 是 Mathlib 中的一个引理，位于命名空间 `exteriorPower`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ιMulti_apply_coe (a : Fin n → M) : ιMulti R n a = ExteriorAlgebra.ιMulti R n a := rfl

/-- Given a linearly ordered family `v` of vectors of `M` and a natural number `n`, produce the
family of `n`fold exterior products of elements of `v`, seen as members of the
`n`th exterior power. -/
/-
**exteriorPower.** 是 Mathlib 中的一个定义，位于命名空间 `exteriorPower`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a linearly ordered family `v` of vectors of `M` and a natural number `n`, 
produce the
family of `n`fold exterior products of elements of `v`, seen as members of the
`n`th exterior power.
-/
noncomputable def ιMulti_family {I : Type*} [LinearOrder I] (v : I → M)
    (s : powersetCard I n) : ⋀[R]^n M :=
  ιMulti R n (v ∘ (ofFinEmbEquiv.symm s))
/-
**exteriorPower.** 是 Mathlib 中的一个引理，位于命名空间 `exteriorPower`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ιMulti_family_eq_coe_comp {I : Type*} [LinearOrder I] (v : I → M) :
    ExteriorAlgebra.ιMulti_family R n v = (↑) ∘ ιMulti_family R n v :=
  rfl
/-
**exteriorPower.** 是 Mathlib 中的一个引理，位于命名空间 `exteriorPower`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ιMulti_family_apply_coe {I : Type*} [LinearOrder I] (v : I → M)
    (s : powersetCard I n) :
    ιMulti_family R n v s = ExteriorAlgebra.ιMulti_family R n v s := rfl

variable (M)
/-- The image of `ExteriorAlgebra.ιMulti R n` spans the `n`th exterior power. Variant of
`ExteriorAlgebra.ιMulti_span_fixedDegree`, useful in rewrites. -/
/-
**exteriorPower.** 是 Mathlib 中的一个引理，位于命名空间 `exteriorPower`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of `ExteriorAlgebra.ιMulti R n` spans the `n`th exterior power. Varian
t of
`ExteriorAlgebra.ιMulti_span_fixedDegree`, useful in rewrites.
-/
lemma ιMulti_span_fixedDegree :
    Submodule.span R (Set.range (ExteriorAlgebra.ιMulti R n)) = ⋀[R]^n M :=
  ExteriorAlgebra.ιMulti_span_fixedDegree R n

open Set Submodule in
/-- If a set `s` spans the module `M`, then the set of all elements of the form `x₁ ∧ ⋯ ∧ xₙ`
where `xᵢ ∈ s` spans `⋀ⁿ M`. -/
/-
**exteriorPower.** 是 Mathlib 中的一个引理，位于命名空间 `exteriorPower`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a set `s` spans the module `M`, then the set of all elements of the form `x₁ 
∧ ⋯ ∧ xₙ`
where `xᵢ ∈ s` spans `⋀ⁿ M`.
-/
lemma ιMulti_span_fixedDegree_of_span_eq_top {s : Set M} (hs : span R s = ⊤) :
    span R (ExteriorAlgebra.ιMulti R n '' {a | range a ⊆ s}) = ⋀[R]^n M := by
  apply le_antisymm
  · rw [span_le]
    rintro - ⟨y, ⟨y_mem, rfl⟩⟩
    apply ExteriorAlgebra.ιMulti_range R n
    simp
  · rw [ExteriorAlgebra.exteriorPower, LinearMap.range_eq_map, ← hs, map_span, span_pow, span_le]
    rintro x hx
    obtain ⟨f, rfl⟩ := Set.mem_pow.mp hx
    refine mem_span_of_mem ⟨ExteriorAlgebra.ιInv ∘ Subtype.val ∘ f, ?_, ?_⟩
    · rw [Set.mem_ofPred_eq, Set.range_comp, Set.image_subset_iff]
      apply Subset.trans ?_ (s.image_subset_preimage_of_inverse ExteriorAlgebra.ι_leftInverse)
      grind
    · rw [ExteriorAlgebra.ιMulti_apply]
      apply congrArg (List.prod ∘ List.ofFn)
      ext i
      obtain ⟨m, -, hm⟩ := (Set.mem_image _ _ _).mp (f i).2
      rw [Function.comp_apply, Function.comp_apply, ← hm, ExteriorAlgebra.ι_leftInverse]

/-- The image of `exteriorPower.ιMulti` spans `⋀[R]^n M`. -/
/-
**exteriorPower.** 是 Mathlib 中的一个引理，位于命名空间 `exteriorPower`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of `exteriorPower.ιMulti` spans `⋀[R]^n M`.
-/
lemma ιMulti_span :
    Submodule.span R (Set.range (ιMulti R n)) = (⊤ : Submodule R (⋀[R]^n M)) := by
  apply LinearMap.map_injective (Submodule.ker_subtype (⋀[R]^n M))
  rw [LinearMap.map_span, ← Set.image_univ, Set.image_image]
  simp only [Submodule.coe_subtype, ιMulti_apply_coe, Set.image_univ, Submodule.map_top,
    Submodule.range_subtype]
  exact ExteriorAlgebra.ιMulti_span_fixedDegree R n

open Set Submodule in
/-- A version of `ιMulti_span_fixedDegree_of_span_eq_top` that works in the exterior power. -/
/-
**exteriorPower.** 是 Mathlib 中的一个引理，位于命名空间 `exteriorPower`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `ιMulti_span_fixedDegree_of_span_eq_top` that works in the exterior
 power.
-/
lemma ιMulti_span_of_span {s : Set M} (hs : span R s = ⊤) :
    span R (ιMulti R n '' {a | range a ⊆ s}) = ⊤ := by
  apply LinearMap.map_injective (ker_subtype (⋀[R]^n M))
  simpa [LinearMap.map_span, Set.image_image] using ιMulti_span_fixedDegree_of_span_eq_top R n M hs

namespace presentation

/-- The index type for the relations in the standard presentation of `⋀[R]^n M`,
in the particular case `ι` is `Fin n`. -/
/-
**exteriorPower.presentation.Rels** 是 Mathlib 中的一个归纳类型，位于命名空间 `exteriorPower.pre
sentation`。
形式化陈述：Type u → Type u_4 → Type u_5 → Type (max (max u u_4) u_5)
参数：max (max u u_4) u_5。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The index type for the relations in the standard presentation of `⋀[R]^n M`,
in the particular case `ι` is `Fin n`.
-/
inductive Rels (ι : Type*) (M : Type*)
  | add (m : ι → M) (i : ι) (x y : M)
  | smul (m : ι → M) (i : ι) (r : R) (x : M)
  | alt (m : ι → M) (i j : ι) (hm : m i = m j) (hij : i ≠ j)

/-- The relations in the standard presentation of `⋀[R]^n M` with generators and relations. -/
@[simps]
/-
**exteriorPower.presentation.relations** 是 Mathlib 中的一个定义，位于命名空间 `exteriorPower.
presentation`。
形式化陈述：relations (ι : Type*) [DecidableEq ι] (M : Type*) [AddCommGroup M] [Module
 R M] : Module.Relations R where G
参数：ι : Type*；M : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The relations in the standard presentation of `⋀[R]^n M` with generators and rel
ations.
-/
noncomputable def relations (ι : Type*) [DecidableEq ι] (M : Type*)
    [AddCommGroup M] [Module R M] :
    Module.Relations R where
  G := ι → M
  R := Rels R ι M
  relation
    | .add m i x y => Finsupp.single (update m i x) 1 +
        Finsupp.single (update m i y) 1 -
        Finsupp.single (update m i (x + y)) 1
    | .smul m i r x => Finsupp.single (update m i (r • x)) 1 -
        r • Finsupp.single (update m i x) 1
    | .alt m _ _ _ _ => Finsupp.single m 1

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {R} in
/-- The solutions in a module `N` to the linear equations
given by `exteriorPower.relations R ι M` identify to alternating maps to `N`. -/
@[simps!]
/-
**exteriorPower.presentation.relationsSolutionEquiv** 是 Mathlib 中的一个定义，位于命名空间 `e
xteriorPower.presentation`。
形式化陈述：relationsSolutionEquiv {ι : Type*} [DecidableEq ι] {M : Type*} [AddCommGro
up M] [Module R M] : (relations R ι M).Solution N ≃ AlternatingMap R M N ι where
 toFun s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The solutions in a module `N` to the linear equations
given by `exteriorPower.relations R ι M` identify to alternating maps to `N`.
-/
noncomputable def relationsSolutionEquiv {ι : Type*} [DecidableEq ι] {M : Type*}
    [AddCommGroup M] [Module R M] :
    (relations R ι M).Solution N ≃ AlternatingMap R M N ι where
  toFun s :=
    { toFun := fun m ↦ s.var m
      map_update_add' := fun m i x y ↦ by
        have := s.linearCombination_var_relation (.add m i x y)
        dsimp at this ⊢
        rw [map_sub, map_add, Finsupp.linearCombination_single, one_smul,
          Finsupp.linearCombination_single, one_smul,
          Finsupp.linearCombination_single, one_smul, sub_eq_zero] at this
        convert! this.symm -- `convert` is necessary due to the implementation of `MultilinearMap`
      map_update_smul' := fun m i r x ↦ by
        have := s.linearCombination_var_relation (.smul m i r x)
        dsimp at this ⊢
        rw [Finsupp.smul_single, smul_eq_mul, mul_one, map_sub,
          Finsupp.linearCombination_single, one_smul,
          Finsupp.linearCombination_single, sub_eq_zero] at this
        convert! this
      map_eq_zero_of_eq' := fun v i j hm hij ↦
        by simpa using s.linearCombination_var_relation (.alt v i j hm hij) }
  invFun f :=
    { var := fun m ↦ f m
      linearCombination_var_relation := by
        rintro (⟨m, i, x, y⟩ | ⟨m, i, r, x⟩ | ⟨v, i, j, hm, hij⟩)
        · simp
        · simp
        · simpa using f.map_eq_zero_of_eq v hm hij }

set_option backward.isDefEq.respectTransparency.types false in
/-- The universal property of the exterior power. -/
/-
**exteriorPower.presentation.isPresentationCore** 是 Mathlib 中的一个定义，位于命名空间 `exter
iorPower.presentation`。
形式化陈述：isPresentationCore : (relationsSolutionEquiv.symm (ιMulti R n (M
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The universal property of the exterior power.
-/
noncomputable def isPresentationCore :
    (relationsSolutionEquiv.symm (ιMulti R n (M := M))).IsPresentationCore where
  desc s := LinearMap.comp (ExteriorAlgebra.liftAlternating
      (Function.update 0 n (relationsSolutionEquiv s))) (Submodule.subtype _)
  postcomp_desc s := by aesop
  postcomp_injective {N _ _ f f' h} := by
    rw [Submodule.linearMap_eq_iff_of_span_eq_top _ _ (ιMulti_span R n M)]
    rintro ⟨_, ⟨f, rfl⟩⟩
    exact Module.Relations.Solution.congr_var h f

end presentation

/-- The standard presentation of the `R`-module `⋀[R]^n M`. -/
@[simps! G R relation var]
/-
**exteriorPower.presentation** 是 Mathlib 中的一个定义，位于命名空间 `exteriorPower`。
形式化陈述：presentation : Module.Presentation R (⋀[R]^n M)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The standard presentation of the `R`-module `⋀[R]^n M`.
-/
noncomputable def presentation : Module.Presentation R (⋀[R]^n M) :=
  .ofIsPresentation (presentation.isPresentationCore R n M).isPresentation

variable {R M n}

/-- Two linear maps on `⋀[R]^n M` that agree on the image of `exteriorPower.ιMulti`
are equal. -/
@[ext]
/-
**exteriorPower.linearMap_ext** 是 Mathlib 中的一个引理，位于命名空间 `exteriorPower`。
形式化陈述：linearMap_ext {f : ⋀[R]^n M ->ₗ[R] N} {g : ⋀[R]^n M ->ₗ[R] N} (heq : f.com
pAlternatingMap (ιMulti R n) = g.compAlternatingMap (ιMulti R n)) : f = g
参数：heq : f.compAlternatingMap (ιMulti R n) = g.compAlternatingMap (ιMulti R n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Relations.Solution.IsPresentation.postcomp_injective`：postcomp_in
jective {f f' : M ->ₗ[A] N} (h' : solution.postcomp f = solution.postcomp f') : 
f = f'
· 使用定理 `Module.Presentation.toIsPresentation`：∀ {A : Type u} [inst : Ring A] {M 
: Type v} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module A M]   (self : Modul
e.Presentation A M), self.…
· 使用定理 `Module.Relations.Solution.ext`：∀ {A : Type u} {inst : Ring A} {relations
 : Module.Relations A} {M : Type v} {inst_1 : AddCommGroup M}   {inst_2 : _root_
.Module A M} {x y :…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x

--- 原说明 ---
Two linear maps on `⋀[R]^n M` that agree on the image of `exteriorPower.ιMulti`
are equal.
-/
lemma linearMap_ext {f : ⋀[R]^n M →ₗ[R] N} {g : ⋀[R]^n M →ₗ[R] N}
    (heq : f.compAlternatingMap (ιMulti R n) = g.compAlternatingMap (ιMulti R n)) : f = g :=
  (presentation R n M).postcomp_injective (by ext f; apply DFunLike.congr_fun heq)

/-- The linear equivalence between `n`-fold alternating maps from `M` to `N` and linear maps from
`⋀[R]^n M` to `N`: this is the universal property of the `n`th exterior power of `M`. -/
/-
**exteriorPower.alternatingMapLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `exteriorPow
er`。
形式化陈述：alternatingMapLinearEquiv : (M [⋀^Fin n]->ₗ[R] N) ≃ₗ[R] ⋀[R]^n M ->ₗ[R] N
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
The linear equivalence between `n`-fold alternating maps from `M` to `N` and lin
ear maps from
`⋀[R]^n M` to `N`: this is the universal property of the `n`th exterior power of
 `M`.
-/
noncomputable def alternatingMapLinearEquiv : (M [⋀^Fin n]→ₗ[R] N) ≃ₗ[R] ⋀[R]^n M →ₗ[R] N :=
  LinearEquiv.symm
    (Equiv.toLinearEquiv
      ((presentation R n M).linearMapEquiv.trans presentation.relationsSolutionEquiv)
      { map_add := fun _ _ => rfl
        map_smul := fun _ _ => rfl })

@[simp]
/-
**exteriorPower.alternatingMapLinearEquiv_comp_** 是 Mathlib 中的一个引理，位于命名空间 `exter
iorPower`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma alternatingMapLinearEquiv_comp_ιMulti (f : M [⋀^Fin n]→ₗ[R] N) :
    (alternatingMapLinearEquiv f).compAlternatingMap (ιMulti R n) = f := by
  obtain ⟨φ, rfl⟩ := alternatingMapLinearEquiv.symm.surjective f
  dsimp [alternatingMapLinearEquiv]
  simp only [LinearEquiv.symm_apply_apply]
  rfl

@[simp]
/-
**exteriorPower.alternatingMapLinearEquiv_apply_** 是 Mathlib 中的一个引理，位于命名空间 `exte
riorPower`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma alternatingMapLinearEquiv_apply_ιMulti (f : M [⋀^Fin n]→ₗ[R] N) (a : Fin n → M) :
    alternatingMapLinearEquiv f (ιMulti R n a) = f a :=
  DFunLike.congr_fun (alternatingMapLinearEquiv_comp_ιMulti f) a

@[simp]
/-
**exteriorPower.alternatingMapLinearEquiv_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `
exteriorPower`。
形式化陈述：alternatingMapLinearEquiv_symm_apply (F : ⋀[R]^n M ->ₗ[R] N) (m : Fin n ->
 M) : alternatingMapLinearEquiv.symm F m = F.compAlternatingMap (ιMulti R n) m
参数：F : ⋀[R]^n M ->ₗ[R] N；m : Fin n -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.surjective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {
M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMono
id M] [inst_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
· 使用引理 `exteriorPower.alternatingMapLinearEquiv_comp_ιMulti`：alternatingMapLinea
rEquiv_comp_ιMulti (f : M [⋀^Fin n]->ₗ[R] N) : (alternatingMapLinearEquiv f).com
pAlternatingMap (ιMulti R n) = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma alternatingMapLinearEquiv_symm_apply (F : ⋀[R]^n M →ₗ[R] N) (m : Fin n → M) :
    alternatingMapLinearEquiv.symm F m = F.compAlternatingMap (ιMulti R n) m := by
  obtain ⟨f, rfl⟩ := alternatingMapLinearEquiv.surjective F
  simp only [LinearEquiv.symm_apply_apply, alternatingMapLinearEquiv_comp_ιMulti]

@[simp]
/-
**exteriorPower.alternatingMapLinearEquiv_** 是 Mathlib 中的一个引理，位于命名空间 `exteriorPo
wer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma alternatingMapLinearEquiv_ιMulti :
    alternatingMapLinearEquiv (ιMulti R n (M := M)) = LinearMap.id := by
  ext
  simp only [alternatingMapLinearEquiv_comp_ιMulti, ιMulti_apply_coe,
    LinearMap.compAlternatingMap_apply, LinearMap.id_coe, id_eq]

/-- If `f` is an alternating map from `M` to `N`,
`alternatingMapLinearEquiv f` is the corresponding linear map from `⋀[R]^n M` to `N`,
and if `g` is a linear map from `N` to `N'`, then
the alternating map `g.compAlternatingMap f` from `M` to `N'` corresponds to the linear
map `g.comp (alternatingMapLinearEquiv f)` on `⋀[R]^n M`. -/
/-
**exteriorPower.alternatingMapLinearEquiv_comp** 是 Mathlib 中的一个引理，位于命名空间 `exteri
orPower`。
形式化陈述：alternatingMapLinearEquiv_comp (g : N ->ₗ[R] N') (f : M [⋀^Fin n]->ₗ[R] N)
 : alternatingMapLinearEquiv (g.compAlternatingMap f) = g.comp (alternatingMapLi
nearEquiv f)
参数：g : N ->ₗ[R] N'；f : M [⋀^Fin n]->ₗ[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `exteriorPower.linearMap_ext`：linearMap_ext {f : ⋀[R]^n M ->ₗ[R] N} {g : 
⋀[R]^n M ->ₗ[R] N} (heq : f.compAlternatingMap (ιMulti R n) = g.compAlternatingM
ap (ιMulti R n)) …
· 使用定理 `AlternatingMap.ext`：ext {f f' : M [⋀^ι]->ₗ[R] N} (H : forall x, f x = f'
 x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `exteriorPower.alternatingMapLinearEquiv_comp_ιMulti`：alternatingMapLinea
rEquiv_comp_ιMulti (f : M [⋀^Fin n]->ₗ[R] N) : (alternatingMapLinearEquiv f).com
pAlternatingMap (ιMulti R n) = f
· 使用引理 `exteriorPower.alternatingMapLinearEquiv_apply_ιMulti`：alternatingMapLine
arEquiv_apply_ιMulti (f : M [⋀^Fin n]->ₗ[R] N) (a : Fin n -> M) : alternatingMap
LinearEquiv f (ιMulti R n a) = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `f` is an alternating map from `M` to `N`,
`alternatingMapLinearEquiv f` is the corresponding linear map from `⋀[R]^n M` to
 `N`,
and if `g` is a linear map from `N` to `N'`, then
the alternating map `g.compAlternatingMap f` from `M` to `N'` corresponds to the
 linear
map `g.comp (alternatingMapLinearEquiv f)` on `⋀[R]^n M`.
-/
lemma alternatingMapLinearEquiv_comp (g : N →ₗ[R] N') (f : M [⋀^Fin n]→ₗ[R] N) :
    alternatingMapLinearEquiv (g.compAlternatingMap f) = g.comp (alternatingMapLinearEquiv f) := by
  ext
  simp only [alternatingMapLinearEquiv_comp_ιMulti, LinearMap.compAlternatingMap_apply,
    LinearMap.coe_comp, comp_apply, alternatingMapLinearEquiv_apply_ιMulti]

/-! Functoriality of the exterior powers. -/

variable (n) in
/-- The linear map between `n`th exterior powers induced by a linear map between the modules. -/
/-
**exteriorPower.map** 是 Mathlib 中的一个定义，位于命名空间 `exteriorPower`。
形式化陈述：map (f : M ->ₗ[R] N) : ⋀[R]^n M ->ₗ[R] ⋀[R]^n N
参数：f : M ->ₗ[R] N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear map between `n`th exterior powers induced by a linear map between the
 modules.
-/
noncomputable def map (f : M →ₗ[R] N) : ⋀[R]^n M →ₗ[R] ⋀[R]^n N :=
  alternatingMapLinearEquiv ((ιMulti R n).compLinearMap f)
/-
**exteriorPower.alternatingMapLinearEquiv_symm_map** 是 Mathlib 中的一个定理，位于命名空间 `ex
teriorPower`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {n : ℕ} {M : Type u_1} {N : Type u_2} [
inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCommGroup N
] [inst_4 : _root_.Module R N] (f : M →ₗ[R] N),   exteriorPower.alternatingMapLi
nearEquiv.symm (exteriorPower.map n f) = (exteriorPower.ιMulti R n).compLinearMa
p f
参数：f : M →ₗ[R] N；exteriorPower.map n f；exteriorPower.ιMulti R n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma alternatingMapLinearEquiv_symm_map (f : M →ₗ[R] N) :
    alternatingMapLinearEquiv.symm (map n f) = (ιMulti R n).compLinearMap f := by
  simp only [map, LinearEquiv.symm_apply_apply]

@[simp]
/-
**exteriorPower.map_comp_** 是 Mathlib 中的一个定理，位于命名空间 `exteriorPower`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_comp_ιMulti (f : M →ₗ[R] N) :
    (map n f).compAlternatingMap (ιMulti R n) = (ιMulti R n).compLinearMap f := by
  simp only [map, alternatingMapLinearEquiv_comp_ιMulti]

@[simp]
/-
**exteriorPower.map_apply_** 是 Mathlib 中的一个定理，位于命名空间 `exteriorPower`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_apply_ιMulti (f : M →ₗ[R] N) (m : Fin n → M) :
    map n f (ιMulti R n m) = ιMulti R n (f ∘ m) := by
  simp only [map, alternatingMapLinearEquiv_apply_ιMulti, AlternatingMap.compLinearMap_apply,
    Function.comp_def]

@[simp]
/-
**exteriorPower.map_comp_** 是 Mathlib 中的一个引理，位于命名空间 `exteriorPower`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_comp_ιMulti_family {I : Type*} [LinearOrder I] (v : I → M) (f : M →ₗ[R] N) :
    (map n f) ∘ (ιMulti_family R n v) = ιMulti_family R n (f ∘ v) := by
  ext ⟨s, hs⟩
  simp only [ιMulti_family, Function.comp_apply, map_apply_ιMulti]
  rfl

@[simp]
/-
**exteriorPower.map_apply_** 是 Mathlib 中的一个引理，位于命名空间 `exteriorPower`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_apply_ιMulti_family {I : Type*} [LinearOrder I] (v : I → M) (f : M →ₗ[R] N)
    (s : powersetCard I n) :
    (map n f) (ιMulti_family R n v s) = ιMulti_family R n (f ∘ v) s := by
  simp only [ιMulti_family, map, alternatingMapLinearEquiv_apply_ιMulti]
  rfl

@[simp]
/-
**exteriorPower.map_id** 是 Mathlib 中的一个定理，位于命名空间 `exteriorPower`。
形式化陈述：map_id : map n (LinearMap.id (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `exteriorPower.linearMap_ext`：linearMap_ext {f : ⋀[R]^n M ->ₗ[R] N} {g : 
⋀[R]^n M ->ₗ[R] N} (heq : f.compAlternatingMap (ιMulti R n) = g.compAlternatingM
ap (ιMulti R n)) …
· 使用定理 `AlternatingMap.ext`：ext {f f' : M [⋀^ι]->ₗ[R] N} (H : forall x, f x = f'
 x) : f = f'
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `exteriorPower.map_comp_ιMulti`：map_comp_ιMulti (f : M ->ₗ[R] N) : (map n
 f).compAlternatingMap (ιMulti R n) = (ιMulti R n).compLinearMap f
· 使用定理 `AlternatingMap.compLinearMap_id`：compLinearMap_id (f : M [⋀^ι]->ₗ[R] N) 
: f.compLinearMap LinearMap.id = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_id :
    map n (LinearMap.id (R := R) (M := M)) = LinearMap.id := by
  aesop

@[simp]
/-
**exteriorPower.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `exteriorPower`。
形式化陈述：map_comp (f : M ->ₗ[R] N) (g : N ->ₗ[R] N') : map n (g ∘ₗ f) = map n g ∘ₗ 
map n f
参数：f : M ->ₗ[R] N；g : N ->ₗ[R] N'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `exteriorPower.linearMap_ext`：linearMap_ext {f : ⋀[R]^n M ->ₗ[R] N} {g : 
⋀[R]^n M ->ₗ[R] N} (heq : f.compAlternatingMap (ιMulti R n) = g.compAlternatingM
ap (ιMulti R n)) …
· 使用定理 `AlternatingMap.ext`：ext {f f' : M [⋀^ι]->ₗ[R] N} (H : forall x, f x = f'
 x) : f = f'
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `exteriorPower.map_comp_ιMulti`：map_comp_ιMulti (f : M ->ₗ[R] N) : (map n
 f).compAlternatingMap (ιMulti R n) = (ιMulti R n).compLinearMap f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exteriorPower.map_apply_ιMulti`：map_apply_ιMulti (f : M ->ₗ[R] N) (m : F
in n -> M) : map n f (ιMulti R n m) = ιMulti R n (f ∘ m)
-/
theorem map_comp (f : M →ₗ[R] N) (g : N →ₗ[R] N') :
    map n (g ∘ₗ f) = map n g ∘ₗ map n f := by
  aesop

/-! Exactness properties of the exterior power functor. -/

/-- If a linear map has a retraction, then the map it induces on exterior powers is injective. -/
/-
**exteriorPower.map_injective** 是 Mathlib 中的一个引理，位于命名空间 `exteriorPower`。
形式化陈述：map_injective {f : M ->ₗ[R] N} (g : N ->ₗ[R] M) (hg : g ∘ₗ f = .id) : Inje
ctive (map n f)
参数：g : N ->ₗ[R] M；hg : g ∘ₗ f = .id。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.RightInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β} {g : β → α}, Function.RightInverse f g → Function.Injective f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
· 使用定理 `exteriorPower.map_comp`：map_comp (f : M ->ₗ[R] N) (g : N ->ₗ[R] N') : ma
p n (g ∘ₗ f) = map n g ∘ₗ map n f
· 使用定理 `exteriorPower.map_id`：map_id : map n (LinearMap.id (R
· 使用定理 `LinearMap.id_coe`：id_coe : ((LinearMap.id : M ->ₗ[R] M) : M -> M) = _roo
t_.id
· 使用定理 `id_eq`：∀ {α : Sort u_1} (a : α), id a = a

--- 原说明 ---
If a linear map has a retraction, then the map it induces on exterior powers is 
injective.
-/
lemma map_injective {f : M →ₗ[R] N} (g : N →ₗ[R] M) (hg : g ∘ₗ f = .id) :
    Injective (map n f) :=
  RightInverse.injective (g := map n g)
    (fun _ ↦ by rw [← LinearMap.comp_apply, ← map_comp, hg, map_id, LinearMap.id_coe, id_eq])

/-- If the base ring is a field, then any injective linear map induces an injective map on
exterior powers. -/
/-
**exteriorPower.map_injective_field** 是 Mathlib 中的一个引理，位于命名空间 `exteriorPower`。
形式化陈述：map_injective_field {K : Type*} [Field K] [Module K M] [Module K N] {f : M
 ->ₗ[K] N} (hf : Injective f) : Injective (map n f)
参数：hf : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `exteriorPower.map_injective`：map_injective {f : M ->ₗ[R] N} (g : N ->ₗ[R
] M) (hg : g ∘ₗ f = .id) : Injective (map n f)
· 使用定理 `LinearMap.exists_leftInverse_of_injective`：LinearMap.exists_leftInverse_
of_injective (f : V ->ₗ[K] V') (hf_inj : LinearMap.ker f = ⊥) : exists g : V' ->
ₗ[K] V, g.comp f = LinearMap.id
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose

--- 原说明 ---
If the base ring is a field, then any injective linear map induces an injective 
map on
exterior powers.
-/
lemma map_injective_field {K : Type*} [Field K] [Module K M] [Module K N]
    {f : M →ₗ[K] N} (hf : Injective f) :
    Injective (map n f) :=
  map_injective _ (f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hf)).choose_spec

/-- If a linear map is surjective, then the map it induces on exterior powers is surjective. -/
/-
**exteriorPower.map_surjective** 是 Mathlib 中的一个引理，位于命名空间 `exteriorPower`。
形式化陈述：map_surjective {f : M ->ₗ[R] N} (hf : Surjective f) : Surjective (map n f)
参数：hf : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `LinearMap.range_eq_map`：range_eq_map [RingHomSurjective τ₁₂] (f : M ->ₛₗ
[τ₁₂] M₂) : range f = map f ⊤
· 使用引理 `exteriorPower.ιMulti_span`：ιMulti_span : Submodule.span R (Set.range (ιM
ulti R n)) = (⊤ : Submodule R (⋀[R]^n M))
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `LinearMap.coe_compAlternatingMap`：coe_compAlternatingMap (g : N ->ₗ[R] N
₂) (f : M [⋀^ι]->ₗ[R] N) : ⇑(g.compAlternatingMap f) = g ∘ f
· 使用定理 `exteriorPower.map_comp_ιMulti`：map_comp_ιMulti (f : M ->ₗ[R] N) : (map n
 f).compAlternatingMap (ιMulti R n) = (ιMulti R n).compLinearMap f
· 使用定理 `AlternatingMap.coe_compLinearMap`：coe_compLinearMap (f : M [⋀^ι]->ₗ[R] N
) (g : M₂ ->ₗ[R] M) : ⇑(f.compLinearMap g) = f ∘ (g ∘ ·)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Set.range_eq_univ`：range_eq_univ : range f = univ ↔ Surjective f
· 使用定理 `Function.Surjective.comp_left`：∀ {α : Sort u} {β : Sort v} {γ : Sort w} 
{g : β → γ}, Function.Surjective g → Function.Surjective fun x => g ∘ x

--- 原说明 ---
If a linear map is surjective, then the map it induces on exterior powers is sur
jective.
-/
lemma map_surjective {f : M →ₗ[R] N} (hf : Surjective f) :
    Surjective (map n f) := by
  rw [← LinearMap.range_eq_top, LinearMap.range_eq_map, ← ιMulti_span, ← ιMulti_span,
    Submodule.map_span, ← Set.range_comp, ← LinearMap.coe_compAlternatingMap, map_comp_ιMulti,
    AlternatingMap.coe_compLinearMap, Set.range_comp]
  conv_rhs => rw [← Set.image_univ]
  congr
  rw [Set.range_eq_univ]
  exact Surjective.comp_left hf

section ιMulti_family

variable (R)

open Submodule Set in
/-- Given an ordered family of vectors `i ↦ v i` ranging over `i ∈ I`, and indexes
`α₁, α₂, …, αₙ ∈ I` (not necessarily in order) the wedge product `v (α 1) ∧ ⋯ ∧ v (α n)` belongs to
the span of `n`-fold _ordered_ wedge products of elements of the `v i`. -/
/-
**exteriorPower.** 是 Mathlib 中的一个引理，位于命名空间 `exteriorPower`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an ordered family of vectors `i ↦ v i` ranging over `i ∈ I`, and indexes
`α₁, α₂, …, αₙ ∈ I` (not necessarily in order) the wedge product `v (α 1) ∧ ⋯ ∧ 
v (α n)` belongs to
the span of `n`-fold _ordered_ wedge products of elements of the `v i`.
-/
private lemma ιMulti_family_span_fixedDegree_aux
    {I : Type*} [LinearOrder I] (v : I → M) (α : Fin n → I) :
    ExteriorAlgebra.ιMulti R n (v ∘ α) ∈ span R (range (ExteriorAlgebra.ιMulti_family R n v)) := by
  by_cases α_inj : Injective α; swap
  · suffices ExteriorAlgebra.ιMulti R n (v ∘ α) = 0 by simp [this]
    exact AlternatingMap.map_eq_zero_of_not_injective _ _ <| fun h ↦ α_inj (Injective.of_comp h)
  suffices ∃ σ : Equiv.Perm (Fin n), (ExteriorAlgebra.ιMulti R n ((v ∘ α) ∘ σ)) ∈
      Submodule.span R (Set.range (ExteriorAlgebra.ιMulti_family R n v)) by
    obtain ⟨σ, hσ⟩ := this
    rw [AlternatingMap.map_perm] at hσ
    refine (Submodule.smul_mem_iff_of_isUnit _ (r := (σ.sign : R)) ?_).mp hσ
    rw [isUnit_iff_exists_inv]
    use (σ.sign : R)
    norm_cast
    simp only [Int.units_mul_self, Units.val_one, Int.cast_one]
  have α_card : (Finset.image α Finset.univ).card = n :=
    (Finset.card_image_of_injective Finset.univ α_inj).trans (Finset.card_fin n)
  use (Finset.orderIsoOfFin (Finset.image α Finset.univ) α_card).toEquiv.trans
    ((Equiv.setCongr Fintype.coe_image_univ).trans (Equiv.ofInjective α α_inj).symm)
  apply Submodule.mem_span_of_mem
  use ⟨(Finset.image α Finset.univ), α_card⟩
  rw [ExteriorAlgebra.ιMulti_family, Function.comp_assoc]
  congr
  ext i
  simp [Equiv.apply_ofInjective_symm]
  rfl

open Finset in
/-- If a family of vectors spans `M`, then the family of its `n`-fold exterior products spans
`⋀[R]^n M`. Here we work in the exterior algebra. -/
/-
**exteriorPower.** 是 Mathlib 中的一个引理，位于命名空间 `exteriorPower`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a family of vectors spans `M`, then the family of its `n`-fold exterior produ
cts spans
`⋀[R]^n M`. Here we work in the exterior algebra.
-/
lemma ιMulti_family_span_fixedDegree_of_span {I : Type*} [LinearOrder I] {v : I → M}
    (hv : Submodule.span R (Set.range v) = ⊤) :
    Submodule.span R (Set.range (ExteriorAlgebra.ιMulti_family R n v)) = ⋀[R]^n M := by
  apply le_antisymm
  · rw [Submodule.span_le, Set.range_subset_iff]
    intro
    rw [SetLike.mem_coe, ιMulti_family_eq_coe_comp, comp_apply]
    exact Submodule.coe_mem _
  · rw [← ιMulti_span_fixedDegree_of_span_eq_top R n M hv, Submodule.span_le]
    rintro - ⟨f, ⟨f_range, rfl⟩⟩
    rw [Set.mem_ofPred] at f_range
    obtain ⟨α, rfl⟩ := Set.range_subset_range_iff_exists_comp.mp f_range
    exact ιMulti_family_span_fixedDegree_aux R v α

/-- If a family of vectors spans `M`, then the family of its `n`-fold exterior products spans
`⋀[R]^n M`. This is a variant of `ιMulti_family_span_fixedDegree_of_span` where we
work in the exterior power and not the exterior algebra. -/
/-
**exteriorPower.** 是 Mathlib 中的一个引理，位于命名空间 `exteriorPower`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a family of vectors spans `M`, then the family of its `n`-fold exterior produ
cts spans
`⋀[R]^n M`. This is a variant of `ιMulti_family_span_fixedDegree_of_span` where 
we
work in the exterior power and not the exterior algebra.
-/
lemma ιMulti_family_span_of_span {I : Type*} [LinearOrder I]
    {v : I → M} (hv : Submodule.span R (Set.range v) = ⊤) :
    Submodule.span R (Set.range (ιMulti_family R n v)) = ⊤ := by
  apply LinearMap.map_injective (Submodule.ker_subtype (⋀[R]^n M))
  rw [LinearMap.map_span, ← Set.image_univ, Set.image_image]
  simpa using ιMulti_family_span_fixedDegree_of_span R hv

open Set Submodule in
/-- If `v` is a family of vectors of `M` indexed by a linearly ordered type, then the span of the
range of `exteriorPower.ιMulti_family R n v`, i.e., of the family of `n`-fold exterior products
of elements of `v`, is the image of the map of exterior powers induced by the inclusion of
the span of `v` into `M`. -/
/-
**exteriorPower.** 是 Mathlib 中的一个引理，位于命名空间 `exteriorPower`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `v` is a family of vectors of `M` indexed by a linearly ordered type, then th
e span of the
range of `exteriorPower.ιMulti_family R n v`, i.e., of the family of `n`-fold ex
terior products
of elements of `v`, is the image of the map of exterior powers induced by the in
clusion of
the span of `v` into `M`.
-/
lemma ιMulti_family_span {I : Type*} [LinearOrder I] (v : I → M) :
    (map n (span R (range v)).subtype).range = span R (range (ιMulti_family R n v)) := by
  have ⟨f, hf⟩ : ∃ f : I → Submodule.span R (Set.range v), Submodule.subtype _ ∘ f = v :=
    ⟨fun i ↦ ⟨v i, Submodule.subset_span (Set.mem_range_self i)⟩, rfl⟩
  have htop : Submodule.span R (Set.range f) = ⊤ := by
    apply SetLike.coe_injective
    apply Set.image_injective.mpr (Submodule.span R (Set.range v)).injective_subtype
    rw [← Submodule.map_coe, ← Submodule.span_image, ← Set.range_comp, hf,
      ← Submodule.map_coe, ← LinearMap.range_eq_map, Submodule.range_subtype]
  rw [LinearMap.range_eq_map (M := ⋀[R]^n _), ← ιMulti_family_span_of_span _ htop,
    Submodule.map_span, ← Set.range_comp, map_comp_ιMulti_family, hf]

end ιMulti_family

/-! Linear equivalences in degrees 0 and 1. -/

variable (R M) in
/-- The linear equivalence ` ⋀[R]^0 M ≃ₗ[R] R`. -/
@[simps! -isSimp symm_apply]
/-
**exteriorPower.zeroEquiv** 是 Mathlib 中的一个定义，位于命名空间 `exteriorPower`。
形式化陈述：zeroEquiv : ⋀[R]^0 M ≃ₗ[R] R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear equivalence ` ⋀[R]^0 M ≃ₗ[R] R`.
-/
noncomputable def zeroEquiv : ⋀[R]^0 M ≃ₗ[R] R :=
  .ofLinearMap (alternatingMapLinearEquiv (AlternatingMap.constOfIsEmpty R _ _ 1))
    { toFun := fun r ↦ r • (ιMulti _ _ (by rintro ⟨i, hi⟩; simp at hi))
      map_add' := by intros; simp only [add_smul]
      map_smul' := by intros; simp only [smul_eq_mul, mul_smul, RingHom.id_apply] }
    (by aesop) (by aesop)

@[simp]
/-
**exteriorPower.zeroEquiv_** 是 Mathlib 中的一个引理，位于命名空间 `exteriorPower`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma zeroEquiv_ιMulti (f : Fin 0 → M) :
    zeroEquiv R M (ιMulti _ _ f) = 1 := by
  simp [zeroEquiv]
/-
**exteriorPower.zeroEquiv_naturality** 是 Mathlib 中的一个引理，位于命名空间 `exteriorPower`。
形式化陈述：zeroEquiv_naturality (f : M ->ₗ[R] N) : (zeroEquiv R N).comp (map 0 f) = z
eroEquiv R M
参数：f : M ->ₗ[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `exteriorPower.linearMap_ext`：linearMap_ext {f : ⋀[R]^n M ->ₗ[R] N} {g : 
⋀[R]^n M ->ₗ[R] N} (heq : f.compAlternatingMap (ιMulti R n) = g.compAlternatingM
ap (ιMulti R n)) …
· 使用定理 `AlternatingMap.ext`：ext {f f' : M [⋀^ι]->ₗ[R] N} (H : forall x, f x = f'
 x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `exteriorPower.map_apply_ιMulti`：map_apply_ιMulti (f : M ->ₗ[R] N) (m : F
in n -> M) : map n f (ιMulti R n m) = ιMulti R n (f ∘ m)
· 使用引理 `exteriorPower.zeroEquiv_ιMulti`：zeroEquiv_ιMulti (f : Fin 0 -> M) : zero
Equiv R M (ιMulti _ _ f) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma zeroEquiv_naturality (f : M →ₗ[R] N) :
    (zeroEquiv R N).comp (map 0 f) = zeroEquiv R M := by aesop

variable (R M) in
/-- The linear equivalence `M ≃ₗ[R] ⋀[R]^1 M`. -/
@[simps! -isSimp symm_apply]
/-
**exteriorPower.oneEquiv** 是 Mathlib 中的一个定义，位于命名空间 `exteriorPower`。
形式化陈述：oneEquiv : ⋀[R]^1 M ≃ₗ[R] M
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.subsingleton_one`：Subsingleton (Fin 1)

--- 原说明 ---
The linear equivalence `M ≃ₗ[R] ⋀[R]^1 M`.
-/
noncomputable def oneEquiv : ⋀[R]^1 M ≃ₗ[R] M :=
  .ofLinearMap (alternatingMapLinearEquiv (AlternatingMap.ofSubsingleton R M M (0 : Fin 1) .id)) (by
    have h (m : M) : (fun (_ : Fin 1) ↦ m) = update (fun _ ↦ 0) 0 m := by
      ext i
      fin_cases i
      rfl
    exact
      { toFun := fun m ↦ ιMulti _ _ (fun _ ↦ m)
        map_add' := fun m₁ m₂ ↦ by
          rw [h]; nth_rw 2 [h]; nth_rw 3 [h]
          simp only [Fin.isValue, AlternatingMap.map_update_add]
        map_smul' := fun r m ↦ by
          dsimp
          rw [h]; nth_rw 2 [h]
          simp only [Fin.isValue, AlternatingMap.map_update_smul] })
  (by aesop) (by aesop)

@[simp]
/-
**exteriorPower.oneEquiv_** 是 Mathlib 中的一个引理，位于命名空间 `exteriorPower`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma oneEquiv_ιMulti (f : Fin 1 → M) :
    oneEquiv R M (ιMulti _ _ f) = f 0 := by
  simp [oneEquiv]
/-
**exteriorPower.oneEquiv_naturality** 是 Mathlib 中的一个引理，位于命名空间 `exteriorPower`。
形式化陈述：oneEquiv_naturality (f : M ->ₗ[R] N) : (oneEquiv R N).comp (map 1 f) = f.c
omp (oneEquiv R M).toLinearMap
参数：f : M ->ₗ[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `exteriorPower.linearMap_ext`：linearMap_ext {f : ⋀[R]^n M ->ₗ[R] N} {g : 
⋀[R]^n M ->ₗ[R] N} (heq : f.compAlternatingMap (ιMulti R n) = g.compAlternatingM
ap (ιMulti R n)) …
· 使用定理 `AlternatingMap.ext`：ext {f f' : M [⋀^ι]->ₗ[R] N} (H : forall x, f x = f'
 x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `exteriorPower.map_apply_ιMulti`：map_apply_ιMulti (f : M ->ₗ[R] N) (m : F
in n -> M) : map n f (ιMulti R n m) = ιMulti R n (f ∘ m)
· 使用引理 `exteriorPower.oneEquiv_ιMulti`：oneEquiv_ιMulti (f : Fin 1 -> M) : oneEqu
iv R M (ιMulti _ _ f) = f 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma oneEquiv_naturality (f : M →ₗ[R] N) :
    (oneEquiv R N).comp (map 1 f) = f.comp (oneEquiv R M).toLinearMap := by aesop

end exteriorPower

