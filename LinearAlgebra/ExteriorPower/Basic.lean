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

variable (R : Type u) [CommRing R] (n : Nat) {M N N' : Type*}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup N'] [Module R N']

namespace exteriorPower

open Function Set Set.powersetCard

/-! The canonical alternating map from `Fin n → M` to `⋀[R]^n M`. -/

/--
Definition of `ιMulti` / `ιMulti` 的定义

English:
definition ιMulti
  signature: : M [⋀^Fin n]->ₗ[R] (⋀[R]^n M)
  body: (ExteriorAlgebra.ιMulti R n).codRestrict (⋀[R]^n M) fun _ =>
ExteriorAlgebra.ιMulti_range R n Set.mem_range_self _

中文:
定义 ιMulti
  签名: : M [⋀^有限集 n]->ₗ[R] (⋀[R]^n M)
  定义体: (ExteriorAlgebra.ιMulti R n).codRestrict (⋀[R]^n M) fun _ =>
ExteriorAlgebra.ιMulti_range R n Set.mem_range_self _

Depends on / 依赖: ExteriorAlgebra, Set.mem_range_self, codRestrict, mem_range_self
-/
def ιMulti : M [⋀^Fin n]->ₗ[R] (⋀[R]^n M) :=
  (ExteriorAlgebra.ιMulti R n).codRestrict (⋀[R]^n M) fun _ =>
ExteriorAlgebra.ιMulti_range R n Set.mem_range_self _

/--
lemma `ιMulti_apply_coe` / 引理 `ιMulti_apply_coe`

English:
lemma ιMulti_apply_coe
  given: (a : Fin n -> M)
  statement: ιMulti R n a = ExteriorAlgebra.ιMulti R n a
  proof: rfl

中文:
引理 ιMulti_apply_coe
  条件: (a : 有限集 n -> M)
  结论: ιMulti R n a = ExteriorAlgebra.ιMulti R n a
  证明: rfl
-/
@[simp] lemma ιMulti_apply_coe (a : Fin n -> M) : ιMulti R n a = ExteriorAlgebra.ιMulti R n a := rfl

/--
Definition of `ιMulti_family` / `ιMulti_family` 的定义

English:
definition ιMulti_family
  signature: {I : Type*} [LinearOrder I] (v : I -> M)
  body: ιMulti R n (v ∘ (ofFinEmbEquiv.symm s))

中文:
定义 ιMulti_family
  签名: {I : 类型} [线性序 I] (v : I -> M)
  定义体: ιMulti R n (v ∘ (ofFinEmbEquiv.symm s))

Depends on / 依赖: ofFinEmbEquiv, ofFinEmbEquiv.symm
-/
noncomputable def ιMulti_family {I : Type*} [LinearOrder I] (v : I -> M)
    (s : powersetCard I n) : ⋀[R]^n M :=
  ιMulti R n (v ∘ (ofFinEmbEquiv.symm s))

/--
lemma `ιMulti_family_eq_coe_comp` / 引理 `ιMulti_family_eq_coe_comp`

English:
lemma ιMulti_family_eq_coe_comp
  given: {I : Type*} [LinearOrder I] (v : I -> M)
  proof: rfl

中文:
引理 ιMulti_family_eq_coe_comp
  条件: {I : 类型} [线性序 I] (v : I -> M)
  证明: rfl
-/
lemma ιMulti_family_eq_coe_comp {I : Type*} [LinearOrder I] (v : I -> M) :
    ExteriorAlgebra.ιMulti_family R n v = (↑) ∘ ιMulti_family R n v :=
  rfl

/--
lemma `ιMulti_family_apply_coe` / 引理 `ιMulti_family_apply_coe`

English:
lemma ιMulti_family_apply_coe
  statement: {I : Type*} [LinearOrder I] (v : I -> M)
  proof: rfl

中文:
引理 ιMulti_family_apply_coe
  结论: {I : 类型} [线性序 I] (v : I -> M)
  证明: rfl
-/
@[simp] lemma ιMulti_family_apply_coe {I : Type*} [LinearOrder I] (v : I -> M)
    (s : powersetCard I n) :
    ιMulti_family R n v s = ExteriorAlgebra.ιMulti_family R n v s := rfl

variable (M)
/--
lemma `ιMulti_span_fixedDegree` / 引理 `ιMulti_span_fixedDegree`

English:
lemma ιMulti_span_fixedDegree
  proof: ExteriorAlgebra.ιMulti_span_fixedDegree R n

中文:
引理 ιMulti_span_fixedDegree
  证明: ExteriorAlgebra.ιMulti_span_fixedDegree R n

Depends on / 依赖: ExteriorAlgebra
-/
lemma ιMulti_span_fixedDegree :
    Submodule.span R (Set.range (ExteriorAlgebra.ιMulti R n)) = ⋀[R]^n M :=
  ExteriorAlgebra.ιMulti_span_fixedDegree R n

open Set Submodule in
/--
lemma `ιMulti_span_fixedDegree_of_span_eq_top` / 引理 `ιMulti_span_fixedDegree_of_span_eq_top`

English:
lemma ιMulti_span_fixedDegree_of_span_eq_top
  given: {s : Set M} (hs : span R s = ⊤)
  proof: by
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
      rw [Function.comp_apply]; rw [Function.comp_apply]; rw [← hm]; rw [ExteriorAlgebra.ι_leftInverse]

中文:
引理 ιMulti_span_fixedDegree_of_span_eq_top
  条件: {s : 集合 M} (hs : span R s = ⊤)
  证明: by
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
      rw [Function.comp_apply]; rw [Function.comp_apply]; rw [← hm]; rw [ExteriorAlgebra.ι_leftInverse]

Depends on / 依赖: ExteriorAlge, ExteriorAlgebra, ExteriorAlgebra.exteriorPower, LinearMap, LinearMap.range_eq_map, Set.image_subset_iff, Set.mem_ofPred_eq, Set.mem_pow.mp, Set.range_comp, Subset, Subset.trans, Subtype, Subtype.val, exteriorPower, image_subset_iff, image_subset_preimage_of_inverse, le_antisymm, map_span, mem_ofPred_eq, mem_pow
-/
lemma ιMulti_span_fixedDegree_of_span_eq_top {s : Set M} (hs : span R s = ⊤) :
    span R (ExteriorAlgebra.ιMulti R n '' {a | range a subseteq s}) = ⋀[R]^n M := by
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
      rw [Function.comp_apply]; rw [Function.comp_apply]; rw [← hm]; rw [ExteriorAlgebra.ι_leftInverse]

/--
lemma `ιMulti_span` / 引理 `ιMulti_span`

English:
lemma ιMulti_span
  proof: by
  apply LinearMap.map_injective (Submodule.ker_subtype (⋀[R]^n M))
  rw [LinearMap.map_span]; rw [← Set.image_univ]; rw [Set.image_image]
  simp only [Submodule.coe_subtype, ιMulti_apply_coe, Set.image_univ, Submodule.map_top,
    Submodule.range_subtype]
  exact ExteriorAlgebra.ιMulti_span_fixedDegree R n

中文:
引理 ιMulti_span
  证明: by
  apply LinearMap.map_injective (Submodule.ker_subtype (⋀[R]^n M))
  rw [LinearMap.map_span]; rw [← Set.image_univ]; rw [Set.image_image]
  simp only [Submodule.coe_subtype, ιMulti_apply_coe, Set.image_univ, Submodule.map_top,
    Submodule.range_subtype]
  exact ExteriorAlgebra.ιMulti_span_fixedDegree R n

Depends on / 依赖: ExteriorAlgebra, LinearMap, LinearMap.map_injective, LinearMap.map_span, Set.image_image, Set.image_univ, Submodule, Submodule.coe_subtype, Submodule.ker_subtype, Submodule.map_top, Submodule.range_subtype, coe_subtype, image_image, image_univ, ker_subtype, map_injective, map_span, map_top, range_subtype
-/
lemma ιMulti_span :
    Submodule.span R (Set.range (ιMulti R n)) = (⊤ : Submodule R (⋀[R]^n M)) := by
  apply LinearMap.map_injective (Submodule.ker_subtype (⋀[R]^n M))
  rw [LinearMap.map_span]; rw [← Set.image_univ]; rw [Set.image_image]
  simp only [Submodule.coe_subtype, ιMulti_apply_coe, Set.image_univ, Submodule.map_top,
    Submodule.range_subtype]
  exact ExteriorAlgebra.ιMulti_span_fixedDegree R n

open Set Submodule in
/--
lemma `ιMulti_span_of_span` / 引理 `ιMulti_span_of_span`

English:
lemma ιMulti_span_of_span
  given: {s : Set M} (hs : span R s = ⊤)
  proof: by
  apply LinearMap.map_injective (ker_subtype (⋀[R]^n M))
  simpa [LinearMap.map_span, Set.image_image] using ιMulti_span_fixedDegree_of_span_eq_top R n M hs

中文:
引理 ιMulti_span_of_span
  条件: {s : 集合 M} (hs : span R s = ⊤)
  证明: by
  apply LinearMap.map_injective (ker_subtype (⋀[R]^n M))
  simpa [LinearMap.map_span, Set.image_image] using ιMulti_span_fixedDegree_of_span_eq_top R n M hs

Depends on / 依赖: LinearMap, LinearMap.map_injective, LinearMap.map_span, Set.image_image, image_image, ker_subtype, map_injective, map_span
-/
lemma ιMulti_span_of_span {s : Set M} (hs : span R s = ⊤) :
    span R (ιMulti R n '' {a | range a subseteq s}) = ⊤ := by
  apply LinearMap.map_injective (ker_subtype (⋀[R]^n M))
  simpa [LinearMap.map_span, Set.image_image] using ιMulti_span_fixedDegree_of_span_eq_top R n M hs

namespace presentation

/--
Inductive type `Rels` / 归纳类型 `Rels`

English:
inductive Rels
  parameters: (ι : Type*) (M : Type*)
  constructors (3):
    - add: (m : ι -> M) (i : ι) (x y : M)
    - smul: (m : ι -> M) (i : ι) (r : R) (x : M)
    - alt: (m : ι -> M) (i j : ι) (hm : m i = m j) (hij : i != j)

中文:
归纳类型 Rels
  参数: (ι : 类型) (M : 类型)
  构造子 (3 个):
    - add: (m : ι -> M) (i : ι) (x y : M)
    - smul: (m : ι -> M) (i : ι) (r : R) (x : M)
    - alt: (m : ι -> M) (i j : ι) (hm : m i = m j) (hij : i != j)
-/
inductive Rels (ι : Type*) (M : Type*)
  | add (m : ι -> M) (i : ι) (x y : M)
  | smul (m : ι -> M) (i : ι) (r : R) (x : M)
  | alt (m : ι -> M) (i j : ι) (hm : m i = m j) (hij : i != j)

/-- The relations in the standard presentation of `⋀[R]^n M` with generators and relations. -/
@[simps]
/--
Definition of `relations` / `relations` 的定义

English:
definition relations
  signature: (ι : Type*) [DecidableEq ι] (M : Type*)
  body: ι -> M
  R := Rels R ι M
  relation
    | .add m i x y => Finsupp.single (update m i x) 1 +
        Finsupp.single (update m i y) 1 -
        Finsupp.single (update m i (x + y)) 1
    | .smul m i r x => Finsupp.single (update m i (r • x)) 1 -
        r • Finsupp.single (update m i x) 1
    | .alt m _ _ _ _ => Finsupp.single m 1

中文:
定义 relations
  签名: (ι : 类型) [DecidableEq ι] (M : 类型)
  定义体: ι -> M
  R := Rels R ι M
  relation
    | .add m i x y => Finsupp.single (update m i x) 1 +
        Finsupp.single (update m i y) 1 -
        Finsupp.single (update m i (x + y)) 1
    | .smul m i r x => Finsupp.single (update m i (r • x)) 1 -
        r • Finsupp.single (update m i x) 1
    | .alt m _ _ _ _ => Finsupp.single m 1
-/
noncomputable def relations (ι : Type*) [DecidableEq ι] (M : Type*)
    [AddCommGroup M] [Module R M] :
    Module.Relations R where
  G := ι -> M
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
/--
Definition of `relationsSolutionEquiv` / `relationsSolutionEquiv` 的定义

English:
definition relationsSolutionEquiv
  signature: {ι : Type*} [DecidableEq ι] {M : Type*}
  body: { toFun := fun m => s.var m
      map_update_add' := fun m i x y => by
        have := s.linearCombination_var_relation (.add m i x y)
        dsimp at this ⊢
        rw [map_sub]; rw [map_add]; rw [Finsupp.linearCombination_single]; rw [one_smul]; rw [Finsupp.linearCombination_single]; rw [one_smul]; rw [Finsupp.linearCombination_single]; rw [one_smul]; rw [sub_eq_zero] at this
        convert! this.symm -- `convert` is necessary due to the implementation of `MultilinearMap`
      map_update_smul' := fun m i r x => by
        have := s.linearCombination_var_relation (.smul m i r x)
        dsimp at this ⊢
        rw [Finsupp.smul_single]; rw [smul_eq_mul]; rw [mul_one]; rw [map_sub]; rw [Finsupp.linearCombination_single]; rw [one_smul]; rw [Finsupp.linearCombination_single]; rw [sub_eq_zero] at this
        convert! this
      map_eq_zero_of_eq' := fun v i j hm hij =>
        by simpa using s.linearCombination_var_relation (.alt v i j hm hij) }
  invFun f :=
    { var := fun m => f m
      linearCombination_var_relation := by
        rintro (⟨m, i, x, y⟩ | ⟨m, i, r, x⟩ | ⟨v, i, j, hm, hij⟩)
        · simp
        · simp
        · simpa using f.map_eq_zero_of_eq v hm hij }

中文:
定义 relationsSolutionEquiv
  签名: {ι : 类型} [DecidableEq ι] {M : 类型}
  定义体: { toFun := fun m => s.var m
      map_update_add' := fun m i x y => by
        have := s.linearCombination_var_relation (.add m i x y)
        dsimp at this ⊢
        rw [map_sub]; rw [map_add]; rw [Finsupp.linearCombination_single]; rw [one_smul]; rw [Finsupp.linearCombination_single]; rw [one_smul]; rw [Finsupp.linearCombination_single]; rw [one_smul]; rw [sub_eq_zero] at this
        convert! this.symm -- `convert` is necessary due to the implementation of `MultilinearMap`
      map_update_smul' := fun m i r x => by
        have := s.linearCombination_var_relation (.smul m i r x)
        dsimp at this ⊢
        rw [Finsupp.smul_single]; rw [smul_eq_mul]; rw [mul_one]; rw [map_sub]; rw [Finsupp.linearCombination_single]; rw [one_smul]; rw [Finsupp.linearCombination_single]; rw [sub_eq_zero] at this
        convert! this
      map_eq_zero_of_eq' := fun v i j hm hij =>
        by simpa using s.linearCombination_var_relation (.alt v i j hm hij) }
  invFun f :=
    { var := fun m => f m
      linearCombination_var_relation := by
        rintro (⟨m, i, x, y⟩ | ⟨m, i, r, x⟩ | ⟨v, i, j, hm, hij⟩)
        · simp
        · simp
        · simpa using f.map_eq_zero_of_eq v hm hij }

Depends on / 依赖: Finsupp, Finsupp.linearCombination_single, MultilinearMap, convert, implementation, linearCom, linearCombination_single, linearCombination_var_relation, map_add, map_sub, map_update_add, map_update_smul, necessary, one_smul, s.linearCom, s.linearCombination_var_relation, s.var, sub_eq_zero, this.symm
-/
noncomputable def relationsSolutionEquiv {ι : Type*} [DecidableEq ι] {M : Type*}
    [AddCommGroup M] [Module R M] :
    (relations R ι M).Solution N ≃ AlternatingMap R M N ι where
  toFun s :=
    { toFun := fun m => s.var m
      map_update_add' := fun m i x y => by
        have := s.linearCombination_var_relation (.add m i x y)
        dsimp at this ⊢
        rw [map_sub]; rw [map_add]; rw [Finsupp.linearCombination_single]; rw [one_smul]; rw [Finsupp.linearCombination_single]; rw [one_smul]; rw [Finsupp.linearCombination_single]; rw [one_smul]; rw [sub_eq_zero] at this
        convert! this.symm -- `convert` is necessary due to the implementation of `MultilinearMap`
      map_update_smul' := fun m i r x => by
        have := s.linearCombination_var_relation (.smul m i r x)
        dsimp at this ⊢
        rw [Finsupp.smul_single]; rw [smul_eq_mul]; rw [mul_one]; rw [map_sub]; rw [Finsupp.linearCombination_single]; rw [one_smul]; rw [Finsupp.linearCombination_single]; rw [sub_eq_zero] at this
        convert! this
      map_eq_zero_of_eq' := fun v i j hm hij =>
        by simpa using s.linearCombination_var_relation (.alt v i j hm hij) }
  invFun f :=
    { var := fun m => f m
      linearCombination_var_relation := by
        rintro (⟨m, i, x, y⟩ | ⟨m, i, r, x⟩ | ⟨v, i, j, hm, hij⟩)
        · simp
        · simp
        · simpa using f.map_eq_zero_of_eq v hm hij }

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `isPresentationCore` / `isPresentationCore` 的定义

English:
definition isPresentationCore
  signature: :
  body: LinearMap.comp (ExteriorAlgebra.liftAlternating
      (Function.update 0 n (relationsSolutionEquiv s))) (Submodule.subtype _)
  postcomp_desc s := by aesop
  postcomp_injective {N _ _ f f' h} := by
    rw [Submodule.linearMap_eq_iff_of_span_eq_top _ _ (ιMulti_span R n M)]
    rintro ⟨_, ⟨f, rfl⟩⟩
    exact Module.Relations.Solution.congr_var h f

中文:
定义 isPresentationCore
  签名: :
  定义体: LinearMap.comp (ExteriorAlgebra.liftAlternating
      (Function.update 0 n (relationsSolutionEquiv s))) (Submodule.subtype _)
  postcomp_desc s := by aesop
  postcomp_injective {N _ _ f f' h} := by
    rw [Submodule.linearMap_eq_iff_of_span_eq_top _ _ (ιMulti_span R n M)]
    rintro ⟨_, ⟨f, rfl⟩⟩
    exact Module.Relations.Solution.congr_var h f

Depends on / 依赖: IsPresentationCore
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
/--
Definition of `presentation` / `presentation` 的定义

English:
definition presentation
  signature: : Module.Presentation R (⋀[R]^n M)
  body: .ofIsPresentation (presentation.isPresentationCore R n M).isPresentation

中文:
定义 presentation
  签名: : 模.呈现 R (⋀[R]^n M)
  定义体: .ofIsPresentation (presentation.isPresentationCore R n M).isPresentation

Depends on / 依赖: isPresentation, isPresentationCore, ofIsPresentation, presentation, presentation.isPresentationCore
-/
noncomputable def presentation : Module.Presentation R (⋀[R]^n M) :=
  .ofIsPresentation (presentation.isPresentationCore R n M).isPresentation

variable {R M n}

/-- Two linear maps on `⋀[R]^n M` that agree on the image of `exteriorPower.ιMulti`
are equal. -/
@[ext]
/--
lemma `linearMap_ext` / 引理 `linearMap_ext`

English:
lemma linearMap_ext
  statement: {f : ⋀[R]^n M ->ₗ[R] N} {g : ⋀[R]^n M ->ₗ[R] N}
  proof: (presentation R n M).postcomp_injective (by ext f; apply DFunLike.congr_fun heq)

中文:
引理 linearMap_ext
  结论: {f : ⋀[R]^n M ->ₗ[R] N} {g : ⋀[R]^n M ->ₗ[R] N}
  证明: (presentation R n M).postcomp_injective (by ext f; apply DFunLike.congr_fun heq)

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, postcomp_injective, presentation
-/
lemma linearMap_ext {f : ⋀[R]^n M ->ₗ[R] N} {g : ⋀[R]^n M ->ₗ[R] N}
    (heq : f.compAlternatingMap (ιMulti R n) = g.compAlternatingMap (ιMulti R n)) : f = g :=
  (presentation R n M).postcomp_injective (by ext f; apply DFunLike.congr_fun heq)

/--
Definition of `alternatingMapLinearEquiv` / `alternatingMapLinearEquiv` 的定义

English:
definition alternatingMapLinearEquiv
  signature: : (M [⋀^Fin n]->ₗ[R] N) ≃ₗ[R] ⋀[R]^n M ->ₗ[R] N
  body: LinearEquiv.symm
    (Equiv.toLinearEquiv
      ((presentation R n M).linearMapEquiv.trans presentation.relationsSolutionEquiv)
      { map_add := fun _ _ => rfl
        map_smul := fun _ _ => rfl })

@[simp]

中文:
定义 alternatingMapLinearEquiv
  签名: : (M [⋀^有限集 n]->ₗ[R] N) ≃ₗ[R] ⋀[R]^n M ->ₗ[R] N
  定义体: LinearEquiv.symm
    (Equiv.toLinearEquiv
      ((presentation R n M).linearMapEquiv.trans presentation.relationsSolutionEquiv)
      { map_add := fun _ _ => rfl
        map_smul := fun _ _ => rfl })

@[simp]

Depends on / 依赖: Equiv.toLinearEquiv, LinearEquiv, LinearEquiv.symm, linearMapEquiv, linearMapEquiv.trans, map_add, map_smul, presentation, presentation.relationsSolutionEquiv, relationsSolutionEquiv, toLinearEquiv
-/
noncomputable def alternatingMapLinearEquiv : (M [⋀^Fin n]->ₗ[R] N) ≃ₗ[R] ⋀[R]^n M ->ₗ[R] N :=
  LinearEquiv.symm
    (Equiv.toLinearEquiv
      ((presentation R n M).linearMapEquiv.trans presentation.relationsSolutionEquiv)
      { map_add := fun _ _ => rfl
        map_smul := fun _ _ => rfl })

@[simp]
/--
lemma `alternatingMapLinearEquiv_comp_ιMulti` / 引理 `alternatingMapLinearEquiv_comp_ιMulti`

English:
lemma alternatingMapLinearEquiv_comp_ιMulti
  given: (f : M [⋀^Fin n]->ₗ[R] N)
  proof: by
  obtain ⟨φ, rfl⟩ := alternatingMapLinearEquiv.symm.surjective f
  dsimp [alternatingMapLinearEquiv]
  simp only [LinearEquiv.symm_apply_apply]
  rfl

@[simp]

中文:
引理 alternatingMapLinearEquiv_comp_ιMulti
  条件: (f : M [⋀^有限集 n]->ₗ[R] N)
  证明: by
  obtain ⟨φ, rfl⟩ := alternatingMapLinearEquiv.symm.surjective f
  dsimp [alternatingMapLinearEquiv]
  simp only [LinearEquiv.symm_apply_apply]
  rfl

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.symm_apply_apply, alternatingMapLinearEquiv, alternatingMapLinearEquiv.symm.surjective, surjective, symm_apply_apply
-/
lemma alternatingMapLinearEquiv_comp_ιMulti (f : M [⋀^Fin n]->ₗ[R] N) :
    (alternatingMapLinearEquiv f).compAlternatingMap (ιMulti R n) = f := by
  obtain ⟨φ, rfl⟩ := alternatingMapLinearEquiv.symm.surjective f
  dsimp [alternatingMapLinearEquiv]
  simp only [LinearEquiv.symm_apply_apply]
  rfl

@[simp]
/--
lemma `alternatingMapLinearEquiv_apply_ιMulti` / 引理 `alternatingMapLinearEquiv_apply_ιMulti`

English:
lemma alternatingMapLinearEquiv_apply_ιMulti
  given: (f : M [⋀^Fin n]->ₗ[R] N) (a : Fin n -> M)
  proof: DFunLike.congr_fun (alternatingMapLinearEquiv_comp_ιMulti f) a

@[simp]

中文:
引理 alternatingMapLinearEquiv_apply_ιMulti
  条件: (f : M [⋀^有限集 n]->ₗ[R] N) (a : 有限集 n -> M)
  证明: DFunLike.congr_fun (alternatingMapLinearEquiv_comp_ιMulti f) a

@[simp]

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun
-/
lemma alternatingMapLinearEquiv_apply_ιMulti (f : M [⋀^Fin n]->ₗ[R] N) (a : Fin n -> M) :
    alternatingMapLinearEquiv f (ιMulti R n a) = f a :=
  DFunLike.congr_fun (alternatingMapLinearEquiv_comp_ιMulti f) a

@[simp]
/--
lemma `alternatingMapLinearEquiv_symm_apply` / 引理 `alternatingMapLinearEquiv_symm_apply`

English:
lemma alternatingMapLinearEquiv_symm_apply
  given: (F : ⋀[R]^n M ->ₗ[R] N) (m : Fin n -> M)
  proof: by
  obtain ⟨f, rfl⟩ := alternatingMapLinearEquiv.surjective F
  simp only [LinearEquiv.symm_apply_apply, alternatingMapLinearEquiv_comp_ιMulti]

@[simp]

中文:
引理 alternatingMapLinearEquiv_symm_apply
  条件: (F : ⋀[R]^n M ->ₗ[R] N) (m : 有限集 n -> M)
  证明: by
  obtain ⟨f, rfl⟩ := alternatingMapLinearEquiv.surjective F
  simp only [LinearEquiv.symm_apply_apply, alternatingMapLinearEquiv_comp_ιMulti]

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.symm_apply_apply, alternatingMapLinearEquiv, alternatingMapLinearEquiv.surjective, surjective, symm_apply_apply
-/
lemma alternatingMapLinearEquiv_symm_apply (F : ⋀[R]^n M ->ₗ[R] N) (m : Fin n -> M) :
    alternatingMapLinearEquiv.symm F m = F.compAlternatingMap (ιMulti R n) m := by
  obtain ⟨f, rfl⟩ := alternatingMapLinearEquiv.surjective F
  simp only [LinearEquiv.symm_apply_apply, alternatingMapLinearEquiv_comp_ιMulti]

@[simp]
/--
lemma `alternatingMapLinearEquiv_ιMulti` / 引理 `alternatingMapLinearEquiv_ιMulti`

English:
lemma alternatingMapLinearEquiv_ιMulti
  proof: by
  ext
  simp only [alternatingMapLinearEquiv_comp_ιMulti, ιMulti_apply_coe,
    LinearMap.compAlternatingMap_apply, LinearMap.id_coe, id_eq]

中文:
引理 alternatingMapLinearEquiv_ιMulti
  证明: by
  ext
  simp only [alternatingMapLinearEquiv_comp_ιMulti, ιMulti_apply_coe,
    LinearMap.compAlternatingMap_apply, LinearMap.id_coe, id_eq]

Depends on / 依赖: LinearMap, LinearMap.compAlternatingMap_apply, LinearMap.id, LinearMap.id_coe, compAlternatingMap_apply, id_coe, id_eq
-/
lemma alternatingMapLinearEquiv_ιMulti :
    alternatingMapLinearEquiv (ιMulti R n (M := M)) = LinearMap.id := by
  ext
  simp only [alternatingMapLinearEquiv_comp_ιMulti, ιMulti_apply_coe,
    LinearMap.compAlternatingMap_apply, LinearMap.id_coe, id_eq]

/--
lemma `alternatingMapLinearEquiv_comp` / 引理 `alternatingMapLinearEquiv_comp`

English:
lemma alternatingMapLinearEquiv_comp
  given: (g : N ->ₗ[R] N') (f : M [⋀^Fin n]->ₗ[R] N)
  proof: by
  ext
  simp only [alternatingMapLinearEquiv_comp_ιMulti, LinearMap.compAlternatingMap_apply,
    LinearMap.coe_comp, comp_apply, alternatingMapLinearEquiv_apply_ιMulti]

中文:
引理 alternatingMapLinearEquiv_comp
  条件: (g : N ->ₗ[R] N') (f : M [⋀^有限集 n]->ₗ[R] N)
  证明: by
  ext
  simp only [alternatingMapLinearEquiv_comp_ιMulti, LinearMap.compAlternatingMap_apply,
    LinearMap.coe_comp, comp_apply, alternatingMapLinearEquiv_apply_ιMulti]

Depends on / 依赖: LinearMap, LinearMap.coe_comp, LinearMap.compAlternatingMap_apply, coe_comp, compAlternatingMap_apply, comp_apply
-/
lemma alternatingMapLinearEquiv_comp (g : N ->ₗ[R] N') (f : M [⋀^Fin n]->ₗ[R] N) :
    alternatingMapLinearEquiv (g.compAlternatingMap f) = g.comp (alternatingMapLinearEquiv f) := by
  ext
  simp only [alternatingMapLinearEquiv_comp_ιMulti, LinearMap.compAlternatingMap_apply,
    LinearMap.coe_comp, comp_apply, alternatingMapLinearEquiv_apply_ιMulti]

/-! Functoriality of the exterior powers. -/

variable (n) in
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : M ->ₗ[R] N)
  body: alternatingMapLinearEquiv ((ιMulti R n).compLinearMap f)

中文:
定义 map
  签名: (f : M ->ₗ[R] N)
  定义体: alternatingMapLinearEquiv ((ιMulti R n).compLinearMap f)

Depends on / 依赖: alternatingMapLinearEquiv, compLinearMap
-/
noncomputable def map (f : M ->ₗ[R] N) : ⋀[R]^n M ->ₗ[R] ⋀[R]^n N :=
  alternatingMapLinearEquiv ((ιMulti R n).compLinearMap f)

/--
lemma `alternatingMapLinearEquiv_symm_map` / 引理 `alternatingMapLinearEquiv_symm_map`

English:
lemma alternatingMapLinearEquiv_symm_map
  given: (f : M ->ₗ[R] N)
  proof: by
  simp only [map, LinearEquiv.symm_apply_apply]

@[simp]

中文:
引理 alternatingMapLinearEquiv_symm_map
  条件: (f : M ->ₗ[R] N)
  证明: by
  simp only [map, LinearEquiv.symm_apply_apply]

@[simp]
-/
@[simp] lemma alternatingMapLinearEquiv_symm_map (f : M ->ₗ[R] N) :
    alternatingMapLinearEquiv.symm (map n f) = (ιMulti R n).compLinearMap f := by
  simp only [map, LinearEquiv.symm_apply_apply]

@[simp]
/--
theorem `map_comp_ιMulti` / 定理 `map_comp_ιMulti`

English:
theorem map_comp_ιMulti
  given: (f : M ->ₗ[R] N)
  proof: by
  simp only [map, alternatingMapLinearEquiv_comp_ιMulti]

@[simp]

中文:
定理 map_comp_ιMulti
  条件: (f : M ->ₗ[R] N)
  证明: by
  simp only [map, alternatingMapLinearEquiv_comp_ιMulti]

@[simp]
-/
theorem map_comp_ιMulti (f : M ->ₗ[R] N) :
    (map n f).compAlternatingMap (ιMulti R n) = (ιMulti R n).compLinearMap f := by
  simp only [map, alternatingMapLinearEquiv_comp_ιMulti]

@[simp]
/--
theorem `map_apply_ιMulti` / 定理 `map_apply_ιMulti`

English:
theorem map_apply_ιMulti
  given: (f : M ->ₗ[R] N) (m : Fin n -> M)
  proof: by
  simp only [map, alternatingMapLinearEquiv_apply_ιMulti, AlternatingMap.compLinearMap_apply,
    Function.comp_def]

@[simp]

中文:
定理 map_apply_ιMulti
  条件: (f : M ->ₗ[R] N) (m : 有限集 n -> M)
  证明: by
  simp only [map, alternatingMapLinearEquiv_apply_ιMulti, AlternatingMap.compLinearMap_apply,
    Function.comp_def]

@[simp]

Depends on / 依赖: AlternatingMap, AlternatingMap.compLinearMap_apply, Function, Function.comp_def, compLinearMap_apply, comp_def
-/
theorem map_apply_ιMulti (f : M ->ₗ[R] N) (m : Fin n -> M) :
    map n f (ιMulti R n m) = ιMulti R n (f ∘ m) := by
  simp only [map, alternatingMapLinearEquiv_apply_ιMulti, AlternatingMap.compLinearMap_apply,
    Function.comp_def]

@[simp]
/--
lemma `map_comp_ιMulti_family` / 引理 `map_comp_ιMulti_family`

English:
lemma map_comp_ιMulti_family
  given: {I : Type*} [LinearOrder I] (v : I -> M) (f : M ->ₗ[R] N)
  proof: by
  ext ⟨s, hs⟩
  simp only [ιMulti_family, Function.comp_apply, map_apply_ιMulti]
  rfl

@[simp]

中文:
引理 map_comp_ιMulti_family
  条件: {I : 类型} [线性序 I] (v : I -> M) (f : M ->ₗ[R] N)
  证明: by
  ext ⟨s, hs⟩
  simp only [ιMulti_family, Function.comp_apply, map_apply_ιMulti]
  rfl

@[simp]

Depends on / 依赖: Function, Function.comp_apply, comp_apply
-/
lemma map_comp_ιMulti_family {I : Type*} [LinearOrder I] (v : I -> M) (f : M ->ₗ[R] N) :
    (map n f) ∘ (ιMulti_family R n v) = ιMulti_family R n (f ∘ v) := by
  ext ⟨s, hs⟩
  simp only [ιMulti_family, Function.comp_apply, map_apply_ιMulti]
  rfl

@[simp]
/--
lemma `map_apply_ιMulti_family` / 引理 `map_apply_ιMulti_family`

English:
lemma map_apply_ιMulti_family
  statement: {I : Type*} [LinearOrder I] (v : I -> M) (f : M ->ₗ[R] N)
  proof: by
  simp only [ιMulti_family, map, alternatingMapLinearEquiv_apply_ιMulti]
  rfl

@[simp]

中文:
引理 map_apply_ιMulti_family
  结论: {I : 类型} [线性序 I] (v : I -> M) (f : M ->ₗ[R] N)
  证明: by
  simp only [ιMulti_family, map, alternatingMapLinearEquiv_apply_ιMulti]
  rfl

@[simp]
-/
lemma map_apply_ιMulti_family {I : Type*} [LinearOrder I] (v : I -> M) (f : M ->ₗ[R] N)
    (s : powersetCard I n) :
    (map n f) (ιMulti_family R n v s) = ιMulti_family R n (f ∘ v) s := by
  simp only [ιMulti_family, map, alternatingMapLinearEquiv_apply_ιMulti]
  rfl

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  proof: by
  aesop

@[simp]

中文:
定理 map_id
  证明: by
  aesop

@[simp]

Depends on / 依赖: LinearMap, LinearMap.id
-/
theorem map_id :
    map n (LinearMap.id (R := R) (M := M)) = LinearMap.id := by
  aesop

@[simp]
/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  given: (f : M ->ₗ[R] N) (g : N ->ₗ[R] N')
  proof: by
  aesop

中文:
定理 map_comp
  条件: (f : M ->ₗ[R] N) (g : N ->ₗ[R] N')
  证明: by
  aesop
-/
theorem map_comp (f : M ->ₗ[R] N) (g : N ->ₗ[R] N') :
    map n (g ∘ₗ f) = map n g ∘ₗ map n f := by
  aesop

/-! Exactness properties of the exterior power functor. -/

/--
lemma `map_injective` / 引理 `map_injective`

English:
lemma map_injective
  given: {f : M ->ₗ[R] N} (g : N ->ₗ[R] M) (hg : g ∘ₗ f = .id)
  proof: RightInverse.injective (g := map n g)
    (fun _ => by rw [← LinearMap.comp_apply, ← map_comp, hg, map_id, LinearMap.id_coe, id_eq])

中文:
引理 map_injective
  条件: {f : M ->ₗ[R] N} (g : N ->ₗ[R] M) (hg : g ∘ₗ f = .id)
  证明: RightInverse.injective (g := map n g)
    (fun _ => by rw [← LinearMap.comp_apply, ← map_comp, hg, map_id, LinearMap.id_coe, id_eq])

Depends on / 依赖: LinearMap, LinearMap.comp_apply, LinearMap.id_coe, RightInverse, RightInverse.injective, comp_apply, id_coe, id_eq, injective, map_comp, map_id
-/
lemma map_injective {f : M ->ₗ[R] N} (g : N ->ₗ[R] M) (hg : g ∘ₗ f = .id) :
    Injective (map n f) :=
  RightInverse.injective (g := map n g)
    (fun _ => by rw [← LinearMap.comp_apply, ← map_comp, hg, map_id, LinearMap.id_coe, id_eq])

/--
lemma `map_injective_field` / 引理 `map_injective_field`

English:
lemma map_injective_field
  statement: {K : Type*} [Field K] [Module K M] [Module K N]
  proof: map_injective _ (f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hf)).choose_spec

中文:
引理 map_injective_field
  结论: {K : 类型} [域 K] [模 K M] [模 K N]
  证明: map_injective _ (f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hf)).choose_spec

Depends on / 依赖: LinearMap, LinearMap.ker_eq_bot.mpr, choose_spec, exists_leftInverse_of_injective, f.exists_leftInverse_of_injective, ker_eq_bot, map_injective
-/
lemma map_injective_field {K : Type*} [Field K] [Module K M] [Module K N]
    {f : M ->ₗ[K] N} (hf : Injective f) :
    Injective (map n f) :=
  map_injective _ (f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hf)).choose_spec

/--
lemma `map_surjective` / 引理 `map_surjective`

English:
lemma map_surjective
  given: {f : M ->ₗ[R] N} (hf : Surjective f)
  proof: by
  rw [← LinearMap.range_eq_top]; rw [LinearMap.range_eq_map]; rw [← ιMulti_span]; rw [← ιMulti_span]; rw [Submodule.map_span]; rw [← Set.range_comp]; rw [← LinearMap.coe_compAlternatingMap]; rw [map_comp_ιMulti]; rw [AlternatingMap.coe_compLinearMap]; rw [Set.range_comp]
  conv_rhs => rw [← Set.image_univ]
  congr
  rw [Set.range_eq_univ]
  exact Surjective.comp_left hf

中文:
引理 map_surjective
  条件: {f : M ->ₗ[R] N} (hf : 满射 f)
  证明: by
  rw [← LinearMap.range_eq_top]; rw [LinearMap.range_eq_map]; rw [← ιMulti_span]; rw [← ιMulti_span]; rw [Submodule.map_span]; rw [← Set.range_comp]; rw [← LinearMap.coe_compAlternatingMap]; rw [map_comp_ιMulti]; rw [AlternatingMap.coe_compLinearMap]; rw [Set.range_comp]
  conv_rhs => rw [← Set.image_univ]
  congr
  rw [Set.range_eq_univ]
  exact Surjective.comp_left hf

Depends on / 依赖: AlternatingMap, AlternatingMap.coe_compLinearMap, LinearMap, LinearMap.coe_compAlternatingMap, LinearMap.range_eq_map, LinearMap.range_eq_top, Set.image_univ, Set.range_comp, Set.range_eq_univ, Submodule, Submodule.map_span, Surjective, Surjective.comp_left, coe_compAlternatingMap, coe_compLinearMap, comp_left, conv_rhs, image_univ, map_span, range_comp
-/
lemma map_surjective {f : M ->ₗ[R] N} (hf : Surjective f) :
    Surjective (map n f) := by
  rw [← LinearMap.range_eq_top]; rw [LinearMap.range_eq_map]; rw [← ιMulti_span]; rw [← ιMulti_span]; rw [Submodule.map_span]; rw [← Set.range_comp]; rw [← LinearMap.coe_compAlternatingMap]; rw [map_comp_ιMulti]; rw [AlternatingMap.coe_compLinearMap]; rw [Set.range_comp]
  conv_rhs => rw [← Set.image_univ]
  congr
  rw [Set.range_eq_univ]
  exact Surjective.comp_left hf

section ιMulti_family

variable (R)

open Submodule Set in
/--
lemma `ιMulti_family_span_fixedDegree_aux` / 引理 `ιMulti_family_span_fixedDegree_aux`

English:
lemma ιMulti_family_span_fixedDegree_aux
  proof: by
  by_cases α_inj : Injective α; swap
  · suffices ExteriorAlgebra.ιMulti R n (v ∘ α) = 0 by simp [this]
exact AlternatingMap.map_eq_zero_of_not_injective _ _ fun h => α_inj (Injective.of_comp h)
  suffices exists σ : Equiv.Perm (Fin n), (ExteriorAlgebra.ιMulti R n ((v ∘ α) ∘ σ)) in
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
  rw [ExteriorAlgebra.ιMulti_family]; rw [Function.comp_assoc]
  congr
  ext i
  simp [Equiv.apply_ofInjective_symm]
  rfl

中文:
引理 ιMulti_family_span_fixedDegree_aux
  证明: by
  by_cases α_inj : Injective α; swap
  · suffices ExteriorAlgebra.ιMulti R n (v ∘ α) = 0 by simp [this]
exact AlternatingMap.map_eq_zero_of_not_injective _ _ fun h => α_inj (Injective.of_comp h)
  suffices exists σ : Equiv.Perm (Fin n), (ExteriorAlgebra.ιMulti R n ((v ∘ α) ∘ σ)) in
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
  rw [ExteriorAlgebra.ιMulti_family]; rw [Function.comp_assoc]
  congr
  ext i
  simp [Equiv.apply_ofInjective_symm]
  rfl
-/
private lemma ιMulti_family_span_fixedDegree_aux
    {I : Type*} [LinearOrder I] (v : I -> M) (α : Fin n -> I) :
    ExteriorAlgebra.ιMulti R n (v ∘ α) in span R (range (ExteriorAlgebra.ιMulti_family R n v)) := by
  by_cases α_inj : Injective α; swap
  · suffices ExteriorAlgebra.ιMulti R n (v ∘ α) = 0 by simp [this]
exact AlternatingMap.map_eq_zero_of_not_injective _ _ fun h => α_inj (Injective.of_comp h)
  suffices exists σ : Equiv.Perm (Fin n), (ExteriorAlgebra.ιMulti R n ((v ∘ α) ∘ σ)) in
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
  rw [ExteriorAlgebra.ιMulti_family]; rw [Function.comp_assoc]
  congr
  ext i
  simp [Equiv.apply_ofInjective_symm]
  rfl

open Finset in
/--
lemma `ιMulti_family_span_fixedDegree_of_span` / 引理 `ιMulti_family_span_fixedDegree_of_span`

English:
lemma ιMulti_family_span_fixedDegree_of_span
  statement: {I : Type*} [LinearOrder I] {v : I -> M}
  proof: by
  apply le_antisymm
  · rw [Submodule.span_le, Set.range_subset_iff]
    intro
    rw [SetLike.mem_coe]; rw [ιMulti_family_eq_coe_comp]; rw [comp_apply]
    exact Submodule.coe_mem _
  · rw [← ιMulti_span_fixedDegree_of_span_eq_top R n M hv, Submodule.span_le]
    rintro - ⟨f, ⟨f_range, rfl⟩⟩
    rw [Set.mem_ofPred] at f_range
    obtain ⟨α, rfl⟩ := Set.range_subset_range_iff_exists_comp.mp f_range
    exact ιMulti_family_span_fixedDegree_aux R v α

中文:
引理 ιMulti_family_span_fixedDegree_of_span
  结论: {I : 类型} [线性序 I] {v : I -> M}
  证明: by
  apply le_antisymm
  · rw [Submodule.span_le, Set.range_subset_iff]
    intro
    rw [SetLike.mem_coe]; rw [ιMulti_family_eq_coe_comp]; rw [comp_apply]
    exact Submodule.coe_mem _
  · rw [← ιMulti_span_fixedDegree_of_span_eq_top R n M hv, Submodule.span_le]
    rintro - ⟨f, ⟨f_range, rfl⟩⟩
    rw [Set.mem_ofPred] at f_range
    obtain ⟨α, rfl⟩ := Set.range_subset_range_iff_exists_comp.mp f_range
    exact ιMulti_family_span_fixedDegree_aux R v α

Depends on / 依赖: Set.mem_ofPred, Set.range_subset_iff, Set.range_subset_range_iff_exists_comp.mp, SetLike, SetLike.mem_coe, Submodule, Submodule.coe_mem, Submodule.span_le, coe_mem, comp_apply, f_range, le_antisymm, mem_coe, mem_ofPred, range_subset_iff, range_subset_range_iff_exists_comp, span_le
-/
lemma ιMulti_family_span_fixedDegree_of_span {I : Type*} [LinearOrder I] {v : I -> M}
    (hv : Submodule.span R (Set.range v) = ⊤) :
    Submodule.span R (Set.range (ExteriorAlgebra.ιMulti_family R n v)) = ⋀[R]^n M := by
  apply le_antisymm
  · rw [Submodule.span_le, Set.range_subset_iff]
    intro
    rw [SetLike.mem_coe]; rw [ιMulti_family_eq_coe_comp]; rw [comp_apply]
    exact Submodule.coe_mem _
  · rw [← ιMulti_span_fixedDegree_of_span_eq_top R n M hv, Submodule.span_le]
    rintro - ⟨f, ⟨f_range, rfl⟩⟩
    rw [Set.mem_ofPred] at f_range
    obtain ⟨α, rfl⟩ := Set.range_subset_range_iff_exists_comp.mp f_range
    exact ιMulti_family_span_fixedDegree_aux R v α

/--
lemma `ιMulti_family_span_of_span` / 引理 `ιMulti_family_span_of_span`

English:
lemma ιMulti_family_span_of_span
  statement: {I : Type*} [LinearOrder I]
  proof: by
  apply LinearMap.map_injective (Submodule.ker_subtype (⋀[R]^n M))
  rw [LinearMap.map_span]; rw [← Set.image_univ]; rw [Set.image_image]
  simpa using ιMulti_family_span_fixedDegree_of_span R hv

中文:
引理 ιMulti_family_span_of_span
  结论: {I : 类型} [线性序 I]
  证明: by
  apply LinearMap.map_injective (Submodule.ker_subtype (⋀[R]^n M))
  rw [LinearMap.map_span]; rw [← Set.image_univ]; rw [Set.image_image]
  simpa using ιMulti_family_span_fixedDegree_of_span R hv

Depends on / 依赖: LinearMap, LinearMap.map_injective, LinearMap.map_span, Set.image_image, Set.image_univ, Submodule, Submodule.ker_subtype, image_image, image_univ, ker_subtype, map_injective, map_span
-/
lemma ιMulti_family_span_of_span {I : Type*} [LinearOrder I]
    {v : I -> M} (hv : Submodule.span R (Set.range v) = ⊤) :
    Submodule.span R (Set.range (ιMulti_family R n v)) = ⊤ := by
  apply LinearMap.map_injective (Submodule.ker_subtype (⋀[R]^n M))
  rw [LinearMap.map_span]; rw [← Set.image_univ]; rw [Set.image_image]
  simpa using ιMulti_family_span_fixedDegree_of_span R hv

open Set Submodule in
/--
lemma `ιMulti_family_span` / 引理 `ιMulti_family_span`

English:
lemma ιMulti_family_span
  given: {I : Type*} [LinearOrder I] (v : I -> M)
  proof: by
  have ⟨f, hf⟩ : exists f : I -> Submodule.span R (Set.range v), Submodule.subtype _ ∘ f = v :=
    ⟨fun i => ⟨v i, Submodule.subset_span (Set.mem_range_self i)⟩, rfl⟩
  have htop : Submodule.span R (Set.range f) = ⊤ := by
    apply SetLike.coe_injective
    apply Set.image_injective.mpr (Submodule.span R (Set.range v)).injective_subtype
    rw [← Submodule.map_coe]; rw [← Submodule.span_image]; rw [← Set.range_comp]; rw [hf]; rw [← Submodule.map_coe]; rw [← LinearMap.range_eq_map]; rw [Submodule.range_subtype]
  rw [LinearMap.range_eq_map (M := ⋀[R]^n _), ← ιMulti_family_span_of_span _ htop,
    Submodule.map_span, ← Set.range_comp, map_comp_ιMulti_family, hf]

中文:
引理 ιMulti_family_span
  条件: {I : 类型} [线性序 I] (v : I -> M)
  证明: by
  have ⟨f, hf⟩ : exists f : I -> Submodule.span R (Set.range v), Submodule.subtype _ ∘ f = v :=
    ⟨fun i => ⟨v i, Submodule.subset_span (Set.mem_range_self i)⟩, rfl⟩
  have htop : Submodule.span R (Set.range f) = ⊤ := by
    apply SetLike.coe_injective
    apply Set.image_injective.mpr (Submodule.span R (Set.range v)).injective_subtype
    rw [← Submodule.map_coe]; rw [← Submodule.span_image]; rw [← Set.range_comp]; rw [hf]; rw [← Submodule.map_coe]; rw [← LinearMap.range_eq_map]; rw [Submodule.range_subtype]
  rw [LinearMap.range_eq_map (M := ⋀[R]^n _), ← ιMulti_family_span_of_span _ htop,
    Submodule.map_span, ← Set.range_comp, map_comp_ιMulti_family, hf]

Depends on / 依赖: LinearMap, LinearMap.range_eq_map, Set.image_injective.mpr, Set.mem_range_self, Set.range, Set.range_comp, SetLike, SetLike.coe_injective, Submodule, Submodule.map_coe, Submodule.range_subtype, Submodule.span, Submodule.span_image, Submodule.subset_span, Submodule.subtype, coe_injective, image_injective, injective_subtype, map_coe, mem_range_self
-/
lemma ιMulti_family_span {I : Type*} [LinearOrder I] (v : I -> M) :
    (map n (span R (range v)).subtype).range = span R (range (ιMulti_family R n v)) := by
  have ⟨f, hf⟩ : exists f : I -> Submodule.span R (Set.range v), Submodule.subtype _ ∘ f = v :=
    ⟨fun i => ⟨v i, Submodule.subset_span (Set.mem_range_self i)⟩, rfl⟩
  have htop : Submodule.span R (Set.range f) = ⊤ := by
    apply SetLike.coe_injective
    apply Set.image_injective.mpr (Submodule.span R (Set.range v)).injective_subtype
    rw [← Submodule.map_coe]; rw [← Submodule.span_image]; rw [← Set.range_comp]; rw [hf]; rw [← Submodule.map_coe]; rw [← LinearMap.range_eq_map]; rw [Submodule.range_subtype]
  rw [LinearMap.range_eq_map (M := ⋀[R]^n _), ← ιMulti_family_span_of_span _ htop,
    Submodule.map_span, ← Set.range_comp, map_comp_ιMulti_family, hf]

end ιMulti_family

/-! Linear equivalences in degrees 0 and 1. -/

variable (R M) in
/-- The linear equivalence ` ⋀[R]^0 M ≃ₗ[R] R`. -/
@[simps! -isSimp symm_apply]
/--
Definition of `zeroEquiv` / `zeroEquiv` 的定义

English:
definition zeroEquiv
  signature: : ⋀[R]^0 M ≃ₗ[R] R
  body: .ofLinearMap (alternatingMapLinearEquiv (AlternatingMap.constOfIsEmpty R _ _ 1))
    { toFun := fun r => r • (ιMulti _ _ (by rintro ⟨i, hi⟩; simp at hi))
      map_add' := by intros; simp only [add_smul]
      map_smul' := by intros; simp only [smul_eq_mul, mul_smul, RingHom.id_apply] }
    (by aesop) (by aesop)

@[simp]

中文:
定义 zeroEquiv
  签名: : ⋀[R]^0 M ≃ₗ[R] R
  定义体: .ofLinearMap (alternatingMapLinearEquiv (AlternatingMap.constOfIsEmpty R _ _ 1))
    { toFun := fun r => r • (ιMulti _ _ (by rintro ⟨i, hi⟩; simp at hi))
      map_add' := by intros; simp only [add_smul]
      map_smul' := by intros; simp only [smul_eq_mul, mul_smul, RingHom.id_apply] }
    (by aesop) (by aesop)

@[simp]

Depends on / 依赖: AlternatingMap, AlternatingMap.constOfIsEmpty, RingHom, RingHom.id_apply, add_smul, alternatingMapLinearEquiv, constOfIsEmpty, id_apply, intros, map_add, map_smul, mul_smul, ofLinearMap, smul_eq_mul
-/
noncomputable def zeroEquiv : ⋀[R]^0 M ≃ₗ[R] R :=
  .ofLinearMap (alternatingMapLinearEquiv (AlternatingMap.constOfIsEmpty R _ _ 1))
    { toFun := fun r => r • (ιMulti _ _ (by rintro ⟨i, hi⟩; simp at hi))
      map_add' := by intros; simp only [add_smul]
      map_smul' := by intros; simp only [smul_eq_mul, mul_smul, RingHom.id_apply] }
    (by aesop) (by aesop)

@[simp]
/--
lemma `zeroEquiv_ιMulti` / 引理 `zeroEquiv_ιMulti`

English:
lemma zeroEquiv_ιMulti
  given: (f : Fin 0 -> M)
  proof: by
  simp [zeroEquiv]

中文:
引理 zeroEquiv_ιMulti
  条件: (f : 有限集 0 -> M)
  证明: by
  simp [zeroEquiv]

Depends on / 依赖: zeroEquiv
-/
lemma zeroEquiv_ιMulti (f : Fin 0 -> M) :
    zeroEquiv R M (ιMulti _ _ f) = 1 := by
  simp [zeroEquiv]

/--
lemma `zeroEquiv_naturality` / 引理 `zeroEquiv_naturality`

English:
lemma zeroEquiv_naturality
  given: (f : M ->ₗ[R] N)
  proof: by aesop

中文:
引理 zeroEquiv_naturality
  条件: (f : M ->ₗ[R] N)
  证明: by aesop
-/
lemma zeroEquiv_naturality (f : M ->ₗ[R] N) :
    (zeroEquiv R N).comp (map 0 f) = zeroEquiv R M := by aesop

variable (R M) in
/-- The linear equivalence `M ≃ₗ[R] ⋀[R]^1 M`. -/
@[simps! -isSimp symm_apply]
/--
Definition of `oneEquiv` / `oneEquiv` 的定义

English:
definition oneEquiv
  signature: : ⋀[R]^1 M ≃ₗ[R] M
  body: .ofLinearMap (alternatingMapLinearEquiv (AlternatingMap.ofSubsingleton R M M (0 : Fin 1) .id)) (by
    have h (m : M) : (fun (_ : Fin 1) => m) = update (fun _ => 0) 0 m := by
      ext i
      fin_cases i
      rfl
    exact
      { toFun := fun m => ιMulti _ _ (fun _ => m)
        map_add' := fun m₁ m₂ => by
          rw [h]; nth_rw 2 [h]; nth_rw 3 [h]
          simp only [Fin.isValue, AlternatingMap.map_update_add]
        map_smul' := fun r m => by
          dsimp
          rw [h]; nth_rw 2 [h]
          simp only [Fin.isValue, AlternatingMap.map_update_smul] })
  (by aesop) (by aesop)

@[simp]

中文:
定义 oneEquiv
  签名: : ⋀[R]^1 M ≃ₗ[R] M
  定义体: .ofLinearMap (alternatingMapLinearEquiv (AlternatingMap.ofSubsingleton R M M (0 : Fin 1) .id)) (by
    have h (m : M) : (fun (_ : Fin 1) => m) = update (fun _ => 0) 0 m := by
      ext i
      fin_cases i
      rfl
    exact
      { toFun := fun m => ιMulti _ _ (fun _ => m)
        map_add' := fun m₁ m₂ => by
          rw [h]; nth_rw 2 [h]; nth_rw 3 [h]
          simp only [Fin.isValue, AlternatingMap.map_update_add]
        map_smul' := fun r m => by
          dsimp
          rw [h]; nth_rw 2 [h]
          simp only [Fin.isValue, AlternatingMap.map_update_smul] })
  (by aesop) (by aesop)

@[simp]

Depends on / 依赖: AlternatingMap, AlternatingMap.map_update_add, AlternatingMap.map_update_smul, AlternatingMap.ofSubsingleton, Fin.isValue, alternatingMapLinearEquiv, fin_cases, isValue, map_add, map_smul, map_update_add, map_update_smul, nth_rw, ofLinearMap, ofSubsingleton, update
-/
noncomputable def oneEquiv : ⋀[R]^1 M ≃ₗ[R] M :=
  .ofLinearMap (alternatingMapLinearEquiv (AlternatingMap.ofSubsingleton R M M (0 : Fin 1) .id)) (by
    have h (m : M) : (fun (_ : Fin 1) => m) = update (fun _ => 0) 0 m := by
      ext i
      fin_cases i
      rfl
    exact
      { toFun := fun m => ιMulti _ _ (fun _ => m)
        map_add' := fun m₁ m₂ => by
          rw [h]; nth_rw 2 [h]; nth_rw 3 [h]
          simp only [Fin.isValue, AlternatingMap.map_update_add]
        map_smul' := fun r m => by
          dsimp
          rw [h]; nth_rw 2 [h]
          simp only [Fin.isValue, AlternatingMap.map_update_smul] })
  (by aesop) (by aesop)

@[simp]
/--
lemma `oneEquiv_ιMulti` / 引理 `oneEquiv_ιMulti`

English:
lemma oneEquiv_ιMulti
  given: (f : Fin 1 -> M)
  proof: by
  simp [oneEquiv]

中文:
引理 oneEquiv_ιMulti
  条件: (f : 有限集 1 -> M)
  证明: by
  simp [oneEquiv]

Depends on / 依赖: oneEquiv
-/
lemma oneEquiv_ιMulti (f : Fin 1 -> M) :
    oneEquiv R M (ιMulti _ _ f) = f 0 := by
  simp [oneEquiv]

/--
lemma `oneEquiv_naturality` / 引理 `oneEquiv_naturality`

English:
lemma oneEquiv_naturality
  given: (f : M ->ₗ[R] N)
  proof: by aesop

中文:
引理 oneEquiv_naturality
  条件: (f : M ->ₗ[R] N)
  证明: by aesop
-/
lemma oneEquiv_naturality (f : M ->ₗ[R] N) :
    (oneEquiv R N).comp (map 1 f) = f.comp (oneEquiv R M).toLinearMap := by aesop

end exteriorPower
