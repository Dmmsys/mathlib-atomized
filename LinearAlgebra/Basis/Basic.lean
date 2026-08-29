/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Alexander Bentkamp
-/
module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Basic results on bases

The main goal of this file is to show the equivalence between bases and families of vectors that are
linearly independent and whose span is the whole space.

There are also various lemmas on bases on specific spaces (such as empty or singletons).

## Main results

* `Basis.linearIndependent`: the basis vectors are linear independent.
* `Basis.span_eq`: the basis vectors span the whole space.
* `Basis.mk`: construct a basis out of `v : ι → M` such that `LinearIndependent v` and
  `span (range v) = ⊤`.
-/

@[expose] public section

assert_not_exists Ordinal

noncomputable section

universe u

open Function Set Submodule Finsupp

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

namespace Module.Basis

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

section Properties

/--
theorem `repr_range` / 定理 `repr_range`

English:
theorem repr_range
  statement: LinearMap.range (b.repr : M ->ₗ[R] ι ->₀ R) = Finsupp.supported R R univ
  proof: by
  rw [LinearEquiv.range]; rw [Finsupp.supported_univ]

中文:
定理 repr_range
  结论: LinearMap.range (b.repr : M ->ₗ[R] ι ->₀ R) = Finsupp.supported R R univ
  证明: by
  rw [LinearEquiv.range]; rw [Finsupp.supported_univ]

Depends on / 依赖: Finsupp, Finsupp.supported_univ, LinearEquiv, LinearEquiv.range, supported_univ
-/
theorem repr_range : LinearMap.range (b.repr : M ->ₗ[R] ι ->₀ R) = Finsupp.supported R R univ := by
  rw [LinearEquiv.range]; rw [Finsupp.supported_univ]

/--
theorem `mem_span_repr_support` / 定理 `mem_span_repr_support`

English:
theorem mem_span_repr_support
  given: (m : M)
  statement: m in span R (b '' (b.repr m).support)
  proof: (Finsupp.mem_span_image_iff_linearCombination _).2
    ⟨b.repr m, by simp [Finsupp.mem_supported_support]⟩

中文:
定理 mem_span_repr_support
  条件: (m : M)
  结论: m in span R (b '' (b.repr m).support)
  证明: (Finsupp.mem_span_image_iff_linearCombination _).2
    ⟨b.repr m, by simp [Finsupp.mem_supported_support]⟩

Depends on / 依赖: Finsupp, Finsupp.mem_span_image_iff_linearCombination, Finsupp.mem_supported_support, b.repr, mem_span_image_iff_linearCombination, mem_supported_support
-/
theorem mem_span_repr_support (m : M) : m in span R (b '' (b.repr m).support) :=
  (Finsupp.mem_span_image_iff_linearCombination _).2
    ⟨b.repr m, by simp [Finsupp.mem_supported_support]⟩

/--
theorem `repr_support_subset_of_mem_span` / 定理 `repr_support_subset_of_mem_span`

English:
theorem repr_support_subset_of_mem_span
  statement: (s : Set ι) {m : M}
  proof: by
  rcases (Finsupp.mem_span_image_iff_linearCombination _).1 hm with ⟨l, hl, rfl⟩
  rwa [repr_linearCombination, ← Finsupp.mem_supported R l]

中文:
定理 repr_support_subset_of_mem_span
  结论: (s : Set ι) {m : M}
  证明: by
  rcases (Finsupp.mem_span_image_iff_linearCombination _).1 hm with ⟨l, hl, rfl⟩
  rwa [repr_linearCombination, ← Finsupp.mem_supported R l]

Depends on / 依赖: Finsupp, Finsupp.mem_span_image_iff_linearCombination, Finsupp.mem_supported, mem_span_image_iff_linearCombination, mem_supported, repr_linearCombination
-/
theorem repr_support_subset_of_mem_span (s : Set ι) {m : M}
    (hm : m in span R (b '' s)) : ↑(b.repr m).support subseteq s := by
  rcases (Finsupp.mem_span_image_iff_linearCombination _).1 hm with ⟨l, hl, rfl⟩
  rwa [repr_linearCombination, ← Finsupp.mem_supported R l]

/--
theorem `mem_span_image` / 定理 `mem_span_image`

English:
theorem mem_span_image
  given: {m : M} {s : Set ι}
  statement: m in span R (b '' s) ↔ ↑(b.repr m).support subseteq s
  proof: ⟨repr_support_subset_of_mem_span _ _, fun h =>
    span_mono (Set.image_mono h) (mem_span_repr_support b _)⟩

@[simp]

中文:
定理 mem_span_image
  条件: {m : M} {s : Set ι}
  结论: m in span R (b '' s) ↔ ↑(b.repr m).support subseteq s
  证明: ⟨repr_support_subset_of_mem_span _ _, fun h =>
    span_mono (Set.image_mono h) (mem_span_repr_support b _)⟩

@[simp]

Depends on / 依赖: Set.image_mono, image_mono, mem_span_repr_support, repr_support_subset_of_mem_span, span_mono
-/
theorem mem_span_image {m : M} {s : Set ι} : m in span R (b '' s) ↔ ↑(b.repr m).support subseteq s :=
  ⟨repr_support_subset_of_mem_span _ _, fun h =>
    span_mono (Set.image_mono h) (mem_span_repr_support b _)⟩

@[simp]
/--
theorem `self_mem_span_image` / 定理 `self_mem_span_image`

English:
theorem self_mem_span_image
  given: [Nontrivial R] {i : ι} {s : Set ι}
  proof: by
  simp [mem_span_image, Finsupp.support_single]

中文:
定理 self_mem_span_image
  条件: [Nontrivial R] {i : ι} {s : Set ι}
  证明: by
  simp [mem_span_image, Finsupp.support_single]

Depends on / 依赖: Finsupp, Finsupp.support_single, mem_span_image, support_single
-/
theorem self_mem_span_image [Nontrivial R] {i : ι} {s : Set ι} :
    b i in span R (b '' s) ↔ i in s := by
  simp [mem_span_image, Finsupp.support_single]

/--
theorem `mem_span` / 定理 `mem_span`

English:
theorem mem_span
  given: (x : M)
  statement: x in span R (range b)
  proof: span_mono (image_subset_range _ _) (mem_span_repr_support b x)

@[simp]

中文:
定理 mem_span
  条件: (x : M)
  结论: x in span R (range b)
  证明: span_mono (image_subset_range _ _) (mem_span_repr_support b x)

@[simp]
-/
protected theorem mem_span (x : M) : x in span R (range b) :=
  span_mono (image_subset_range _ _) (mem_span_repr_support b x)

@[simp]
/--
theorem `span_eq` / 定理 `span_eq`

English:
theorem span_eq
  statement: span R (range b) = ⊤
  proof: eq_top_iff.mpr fun x _ => b.mem_span x

中文:
定理 span_eq
  结论: span R (range b) = ⊤
  证明: eq_top_iff.mpr fun x _ => b.mem_span x
-/
protected theorem span_eq : span R (range b) = ⊤ :=
  eq_top_iff.mpr fun x _ => b.mem_span x

/--
theorem `_root_.Submodule.eq_top_iff_forall_basis_mem` / 定理 `_root_.Submodule.eq_top_iff_forall_basis_mem`

English:
theorem _root_.Submodule.eq_top_iff_forall_basis_mem
  given: {p : Submodule R M}
  proof: by
  refine ⟨fun h => by simp [h], fun h => ?_⟩
  replace h : range b subseteq p := by rintro - ⟨i, rfl⟩; exact h i
  simpa using span_mono (R := R) h

中文:
定理 _root_.Submodule.eq_top_iff_forall_basis_mem
  条件: {p : Submodule R M}
  证明: by
  refine ⟨fun h => by simp [h], fun h => ?_⟩
  replace h : range b subseteq p := by rintro - ⟨i, rfl⟩; exact h i
  simpa using span_mono (R := R) h

Depends on / 依赖: replace, span_mono, subseteq
-/
theorem _root_.Submodule.eq_top_iff_forall_basis_mem {p : Submodule R M} :
    p = ⊤ ↔ forall i, b i in p := by
  refine ⟨fun h => by simp [h], fun h => ?_⟩
  replace h : range b subseteq p := by rintro - ⟨i, rfl⟩; exact h i
  simpa using span_mono (R := R) h

/--
theorem `index_nonempty` / 定理 `index_nonempty`

English:
theorem index_nonempty
  given: (b : Basis ι R M) [Nontrivial M]
  statement: Nonempty ι
  proof: by
  obtain ⟨x, y, ne⟩ : exists x y : M, x != y := Nontrivial.exists_pair_ne
  obtain ⟨i, _⟩ := not_forall.mp (mt b.ext_elem_iff.2 ne)
  exact ⟨i⟩

中文:
定理 index_nonempty
  条件: (b : Basis ι R M) [Nontrivial M]
  结论: Nonempty ι
  证明: by
  obtain ⟨x, y, ne⟩ : exists x y : M, x != y := Nontrivial.exists_pair_ne
  obtain ⟨i, _⟩ := not_forall.mp (mt b.ext_elem_iff.2 ne)
  exact ⟨i⟩

Depends on / 依赖: Nontrivial, Nontrivial.exists_pair_ne, b.ext_elem_iff, exists_pair_ne, ext_elem_iff, not_forall, not_forall.mp
-/
theorem index_nonempty (b : Basis ι R M) [Nontrivial M] : Nonempty ι := by
  obtain ⟨x, y, ne⟩ : exists x y : M, x != y := Nontrivial.exists_pair_ne
  obtain ⟨i, _⟩ := not_forall.mp (mt b.ext_elem_iff.2 ne)
  exact ⟨i⟩

/--
theorem `linearIndependent` / 定理 `linearIndependent`

English:
theorem linearIndependent
  statement: LinearIndependent R b
  proof: fun x y hxy => by
    rw [← b.repr_linearCombination x]; rw [hxy]; rw [b.repr_linearCombination y]

中文:
定理 linearIndependent
  结论: LinearIndependent R b
  证明: fun x y hxy => by
    rw [← b.repr_linearCombination x]; rw [hxy]; rw [b.repr_linearCombination y]
-/
protected theorem linearIndependent : LinearIndependent R b :=
  fun x y hxy => by
    rw [← b.repr_linearCombination x]; rw [hxy]; rw [b.repr_linearCombination y]

/--
lemma `linearIndepOn` / 引理 `linearIndepOn`

English:
lemma linearIndepOn
  given: (s : Set ι)
  statement: LinearIndepOn R b s
  proof: b.linearIndependent.linearIndepOn s

中文:
引理 linearIndepOn
  条件: (s : Set ι)
  结论: LinearIndepOn R b s
  证明: b.linearIndependent.linearIndepOn s
-/
protected lemma linearIndepOn (s : Set ι) : LinearIndepOn R b s :=
  b.linearIndependent.linearIndepOn s

/--
theorem `ne_zero` / 定理 `ne_zero`

English:
theorem ne_zero
  given: [Nontrivial R] (i)
  statement: b i != 0
  proof: b.linearIndependent.ne_zero i

中文:
定理 ne_zero
  条件: [Nontrivial R] (i)
  结论: b i != 0
  证明: b.linearIndependent.ne_zero i
-/
protected theorem ne_zero [Nontrivial R] (i) : b i != 0 :=
  b.linearIndependent.ne_zero i

/--
theorem `injective_constr_of_linearIndependent` / 定理 `injective_constr_of_linearIndependent`

English:
theorem injective_constr_of_linearIndependent
  proof: fun _ _ hab => b.repr.injective hv.finsuppLinearCombination_injective by
    simpa [constr_def] using hab

中文:
定理 injective_constr_of_linearIndependent
  证明: fun _ _ hab => b.repr.injective hv.finsuppLinearCombination_injective by
    simpa [constr_def] using hab

Depends on / 依赖: b.repr.injective, constr_def, finsuppLinearCombination_injective, hv.finsuppLinearCombination_injective, injective
-/
theorem injective_constr_of_linearIndependent
    [Semiring R₂] [Module R₂ M'] [SMulCommClass R R₂ M'] {v : ι -> M'}
    (hv : LinearIndependent R v) : Injective (b.constr R₂ v) :=
fun _ _ hab => b.repr.injective hv.finsuppLinearCombination_injective by
    simpa [constr_def] using hab

end Properties

variable {v : ι -> M} {x y : M}

section Mk

variable (hli : LinearIndependent R v) (hsp : ⊤ <= span R (range v))

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def mk
  body: .ofRepr
    { hli.repr.comp (LinearMap.id.codRestrict _ fun _ => hsp Submodule.mem_top) with
      invFun := Finsupp.linearCombination _ v
      left_inv := fun x => hli.linearCombination_repr ⟨x, _⟩
      right_inv := fun _ => hli.repr_eq rfl }

@[simp]

中文:
定义 noncomputable
  签名: def mk
  定义体: .ofRepr
    { hli.repr.comp (LinearMap.id.codRestrict _ fun _ => hsp Submodule.mem_top) with
      invFun := Finsupp.linearCombination _ v
      left_inv := fun x => hli.linearCombination_repr ⟨x, _⟩
      right_inv := fun _ => hli.repr_eq rfl }

@[simp]
-/
protected noncomputable def mk : Basis ι R M :=
  .ofRepr
    { hli.repr.comp (LinearMap.id.codRestrict _ fun _ => hsp Submodule.mem_top) with
      invFun := Finsupp.linearCombination _ v
      left_inv := fun x => hli.linearCombination_repr ⟨x, _⟩
      right_inv := fun _ => hli.repr_eq rfl }

@[simp]
/--
theorem `mk_repr` / 定理 `mk_repr`

English:
theorem mk_repr
  statement: (Basis.mk hli hsp).repr x = hli.repr ⟨x, hsp Submodule.mem_top⟩
  proof: rfl

中文:
定理 mk_repr
  结论: (Basis.mk hli hsp).repr x = hli.repr ⟨x, hsp Submodule.mem_top⟩
  证明: rfl
-/
theorem mk_repr : (Basis.mk hli hsp).repr x = hli.repr ⟨x, hsp Submodule.mem_top⟩ :=
  rfl

/--
theorem `mk_apply` / 定理 `mk_apply`

English:
theorem mk_apply
  given: (i : ι)
  statement: Basis.mk hli hsp i = v i
  proof: show Finsupp.linearCombination _ v _ = v i by simp

@[simp]

中文:
定理 mk_apply
  条件: (i : ι)
  结论: Basis.mk hli hsp i = v i
  证明: show Finsupp.linearCombination _ v _ = v i by simp

@[simp]

Depends on / 依赖: Finsupp, Finsupp.linearCombination, linearCombination
-/
theorem mk_apply (i : ι) : Basis.mk hli hsp i = v i :=
  show Finsupp.linearCombination _ v _ = v i by simp

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  statement: ⇑(Basis.mk hli hsp) = v
  proof: funext (mk_apply _ _)

中文:
定理 coe_mk
  结论: ⇑(Basis.mk hli hsp) = v
  证明: funext (mk_apply _ _)

Depends on / 依赖: mk_apply
-/
theorem coe_mk : ⇑(Basis.mk hli hsp) = v :=
  funext (mk_apply _ _)

end Mk

section Coord

@[simp]
/--
theorem `linearIndependent_coord` / 定理 `linearIndependent_coord`

English:
theorem linearIndependent_coord
  given: {R : Type*} [CommSemiring R] [Module R M] (b : Basis ι R M)
  proof: by
  classical
  refine linearIndependent_iff'ₛ.mpr fun s l₁ l₂ h j hj => ?_
  simpa [hj, Finsupp.single_apply] using congr($h (b j))

中文:
定理 linearIndependent_coord
  条件: {R : 类型} [CommSemiring R] [Module R M] (b : Basis ι R M)
  证明: by
  classical
  refine linearIndependent_iff'ₛ.mpr fun s l₁ l₂ h j hj => ?_
  simpa [hj, Finsupp.single_apply] using congr($h (b j))

Depends on / 依赖: Finsupp, Finsupp.single_apply, classical, linearIndependent_iff, single_apply
-/
theorem linearIndependent_coord {R : Type*} [CommSemiring R] [Module R M] (b : Basis ι R M) :
    LinearIndependent R b.coord := by
  classical
  refine linearIndependent_iff'ₛ.mpr fun s l₁ l₂ h j hj => ?_
  simpa [hj, Finsupp.single_apply] using congr($h (b j))

variable (hli : LinearIndependent R v) (hsp : ⊤ <= span R (range v))

variable {hli hsp}

/--
theorem `mk_coord_apply_eq` / 定理 `mk_coord_apply_eq`

English:
theorem mk_coord_apply_eq
  given: (i : ι)
  statement: (Basis.mk hli hsp).coord i (v i) = 1
  proof: show hli.repr ⟨v i, Submodule.subset_span (mem_range_self i)⟩ i = 1 by simp [hli.repr_eq_single i]

中文:
定理 mk_coord_apply_eq
  条件: (i : ι)
  结论: (Basis.mk hli hsp).coord i (v i) = 1
  证明: show hli.repr ⟨v i, Submodule.subset_span (mem_range_self i)⟩ i = 1 by simp [hli.repr_eq_single i]

Depends on / 依赖: Submodule, Submodule.subset_span, hli.repr, hli.repr_eq_single, mem_range_self, repr_eq_single, subset_span
-/
theorem mk_coord_apply_eq (i : ι) : (Basis.mk hli hsp).coord i (v i) = 1 :=
  show hli.repr ⟨v i, Submodule.subset_span (mem_range_self i)⟩ i = 1 by simp [hli.repr_eq_single i]

/--
theorem `mk_coord_apply_ne` / 定理 `mk_coord_apply_ne`

English:
theorem mk_coord_apply_ne
  given: {i j : ι} (h : j != i)
  statement: (Basis.mk hli hsp).coord i (v j) = 0
  proof: show hli.repr ⟨v j, Submodule.subset_span (mem_range_self j)⟩ i = 0 by
    simp [hli.repr_eq_single j, h]

中文:
定理 mk_coord_apply_ne
  条件: {i j : ι} (h : j != i)
  结论: (Basis.mk hli hsp).coord i (v j) = 0
  证明: show hli.repr ⟨v j, Submodule.subset_span (mem_range_self j)⟩ i = 0 by
    simp [hli.repr_eq_single j, h]

Depends on / 依赖: Submodule, Submodule.subset_span, hli.repr, hli.repr_eq_single, mem_range_self, repr_eq_single, subset_span
-/
theorem mk_coord_apply_ne {i j : ι} (h : j != i) : (Basis.mk hli hsp).coord i (v j) = 0 :=
  show hli.repr ⟨v j, Submodule.subset_span (mem_range_self j)⟩ i = 0 by
    simp [hli.repr_eq_single j, h]

/--
theorem `mk_coord_apply` / 定理 `mk_coord_apply`

English:
theorem mk_coord_apply
  given: [DecidableEq ι] {i j : ι}
  proof: by
  rcases eq_or_ne j i with h | h
  · simp only [h, if_true, mk_coord_apply_eq i]
  · simp only [h, if_false, mk_coord_apply_ne h]

中文:
定理 mk_coord_apply
  条件: [DecidableEq ι] {i j : ι}
  证明: by
  rcases eq_or_ne j i with h | h
  · simp only [h, if_true, mk_coord_apply_eq i]
  · simp only [h, if_false, mk_coord_apply_ne h]

Depends on / 依赖: eq_or_ne, if_false, if_true, mk_coord_apply_eq, mk_coord_apply_ne
-/
theorem mk_coord_apply [DecidableEq ι] {i j : ι} :
    (Basis.mk hli hsp).coord i (v j) = if j = i then 1 else 0 := by
  rcases eq_or_ne j i with h | h
  · simp only [h, if_true, mk_coord_apply_eq i]
  · simp only [h, if_false, mk_coord_apply_ne h]

end Coord

section Span

variable (hli : LinearIndependent R v)

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def span
  body: Basis.mk (linearIndependent_span hli) by
    intro x _
    have : forall i, v i in span R (range v) := fun i => subset_span (Set.mem_range_self _)
    have h₁ : (((↑) : span R (range v) -> M) '' range fun i => ⟨v i, this i⟩) = range v := by
      simp only [← Set.range_comp]
      rfl
    have h₂ : 

中文:
定义 noncomputable
  签名: def span
  定义体: Basis.mk (linearIndependent_span hli) by
    intro x _
    have : forall i, v i in span R (range v) := fun i => subset_span (Set.mem_range_self _)
    have h₁ : (((↑) : span R (range v) -> M) '' range fun i => ⟨v i, this i⟩) = range v := by
      simp only [← Set.range_comp]
      rfl
    have h₂ : 
-/
protected noncomputable def span : Basis ι R (span R (range v)) :=
Basis.mk (linearIndependent_span hli) by
    intro x _
    have : forall i, v i in span R (range v) := fun i => subset_span (Set.mem_range_self _)
    have h₁ : (((↑) : span R (range v) -> M) '' range fun i => ⟨v i, this i⟩) = range v := by
      simp only [← Set.range_comp]
      rfl
    have h₂ : map (Submodule.subtype (span R (range v))) (span R (range fun i => ⟨v i, this i⟩)) =
        span R (range v) := by
      rw [← span_image]; rw [Submodule.coe_subtype]; rw [h₁]
    have h₃ : (x : M) in map (Submodule.subtype (span R (range v)))
        (span R (Set.range fun i => Subtype.mk (v i) (this i))) := by
      rw [h₂]
      apply Subtype.mem x
    rcases mem_map.1 h₃ with ⟨y, hy₁, hy₂⟩
    have h_x_eq_y : x = y := by
      rw [Subtype.ext_iff]; rw [← hy₂]
      simp
    rwa [h_x_eq_y]

@[simp]
/--
theorem `span_apply` / 定理 `span_apply`

English:
theorem span_apply
  given: (i : ι)
  proof: by
  ext
exact congr_arg ((↑) : span R (range v) -> M) Basis.mk_apply _ _ _

中文:
定理 span_apply
  条件: (i : ι)
  证明: by
  ext
exact congr_arg ((↑) : span R (range v) -> M) Basis.mk_apply _ _ _
-/
protected theorem span_apply (i : ι) :
Basis.span hli i = ⟨v i, Submodule.subset_span mem_range_self _⟩ := by
  ext
exact congr_arg ((↑) : span R (range v) -> M) Basis.mk_apply _ _ _

/--
theorem `coe_span_apply` / 定理 `coe_span_apply`

English:
theorem coe_span_apply
  given: (i : ι)
  statement: (Basis.span hli i : M) = v i
  proof: by simp

@[simp]

中文:
定理 coe_span_apply
  条件: (i : ι)
  结论: (Basis.span hli i : M) = v i
  证明: by simp

@[simp]
-/
protected theorem coe_span_apply (i : ι) : (Basis.span hli i : M) = v i := by simp

@[simp]
/--
theorem `span_repr_eq_single` / 定理 `span_repr_eq_single`

English:
theorem span_repr_eq_single
  statement: (i : ι)
  proof: by
  rw [← LinearEquiv.eq_symm_apply]
  simp [Basis.span]

中文:
定理 span_repr_eq_single
  结论: (i : ι)
  证明: by
  rw [← LinearEquiv.eq_symm_apply]
  simp [Basis.span]
-/
protected theorem span_repr_eq_single (i : ι)
    (hi : v i in span R (range v) := subset_span <| mem_range_self i) :
    (Basis.span hli).repr ⟨v i, hi⟩ = single i 1 := by
  rw [← LinearEquiv.eq_symm_apply]
  simp [Basis.span]

/--
lemma `span_neg` / 引理 `span_neg`

English:
lemma span_neg
  statement: {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
  proof: by
  ext; simp

中文:
引理 span_neg
  结论: {R M : 类型} [Ring R] [AddCommGroup M] [Module R M]
  证明: by
  ext; simp

Depends on / 依赖: Basis.span, LinearEquiv, LinearEquiv.neg, hli.neg, neg_range
-/
lemma span_neg {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {v : ι -> M} (hli : LinearIndependent R v)
    (h : span R (range v) = span R (range (-v)) := by simp [← neg_range']) :
    Basis.span hli.neg = ((Basis.span hli).map <| (LinearEquiv.neg _).trans (.ofEq _ _ h)) := by
  ext; simp

end Span

set_option backward.isDefEq.respectTransparency false in
/--
theorem `maximal` / 定理 `maximal`

English:
theorem maximal
  given: [Nontrivial R] (b : Basis ι R M)
  statement: b.linearIndependent.Maximal
  proof: fun w hi h => by
  -- If `w` is strictly bigger than `range b`,
  apply le_antisymm h
  -- then choose some `x ∈ w \ range b`,
  intro x p
  by_contra q
  -- and write it in terms of the basis.
  have e := b.linearCombination_repr x
  -- This then expresses `x` as a linear combination
  -- of elemen

中文:
定理 maximal
  条件: [Nontrivial R] (b : Basis ι R M)
  结论: b.linearIndependent.Maximal
  证明: fun w hi h => by
  -- If `w` is strictly bigger than `range b`,
  apply le_antisymm h
  -- then choose some `x ∈ w \ range b`,
  intro x p
  by_contra q
  -- and write it in terms of the basis.
  have e := b.linearCombination_repr x
  -- This then expresses `x` as a linear combination
  -- of elemen
-/
theorem maximal [Nontrivial R] (b : Basis ι R M) : b.linearIndependent.Maximal := fun w hi h => by
  -- If `w` is strictly bigger than `range b`,
  apply le_antisymm h
  -- then choose some `x ∈ w \ range b`,
  intro x p
  by_contra q
  -- and write it in terms of the basis.
  have e := b.linearCombination_repr x
  -- This then expresses `x` as a linear combination
  -- of elements of `w` which are in the range of `b`,
  let u : ι ↪ w :=
    ⟨fun i => ⟨b i, h ⟨i, rfl⟩⟩, fun i i' r =>
      b.injective (by simpa only [Subtype.mk_eq_mk] using r)⟩
  simp_rw [Finsupp.linearCombination_apply] at e
  change ((b.repr x).sum fun (i : ι) (a : R) => a • (u i : M)) = ((⟨x, p⟩ : w) : M) at e
  rw [← Finsupp.sum_embDomain (f := u) (g := fun x r => r • (x : M))]; rw [← Finsupp.linearCombination_apply] at e
  -- Now we can contradict the linear independence of `hi`
  refine hi.linearCombination_ne_of_notMem_support _ ?_ e
  simp only [Finset.mem_map, Finsupp.support_embDomain]
  rintro ⟨j, -, W⟩
  simp only [u, Embedding.coeFn_mk, Subtype.mk_eq_mk] at W
  apply q ⟨j, W⟩

/--
Instance `uniqueBasis` / 实例 `uniqueBasis`

English:
instance uniqueBasis
  signature: [Subsingleton R]
  body: ⟨⟨⟨default⟩⟩, fun ⟨b⟩ => by rw [Subsingleton.elim b]⟩

中文:
实例 uniqueBasis
  签名: [Subsingleton R]
  定义体: ⟨⟨⟨default⟩⟩, fun ⟨b⟩ => by rw [Subsingleton.elim b]⟩

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
instance uniqueBasis [Subsingleton R] : Unique (Basis ι R M) :=
  ⟨⟨⟨default⟩⟩, fun ⟨b⟩ => by rw [Subsingleton.elim b]⟩

variable (b : Basis ι R M)

section Singleton

/--
Definition of `singleton` / `singleton` 的定义

English:
definition singleton
  signature: (ι R : Type*) [Unique ι] [Semiring R]
  body: ofRepr
    { toFun := fun x => Finsupp.single default x
      invFun := fun f => f default
      left_inv := fun x => by simp
      right_inv := fun f => Finsupp.unique_ext (by simp)
      map_add' := fun x y => by simp
      map_smul' := fun c x => by simp }

中文:
定义 singleton
  签名: (ι R : 类型) [Unique ι] [Semiring R]
  定义体: ofRepr
    { toFun := fun x => Finsupp.single default x
      invFun := fun f => f default
      left_inv := fun x => by simp
      right_inv := fun f => Finsupp.unique_ext (by simp)
      map_add' := fun x y => by simp
      map_smul' := fun c x => by simp }
-/
protected def singleton (ι R : Type*) [Unique ι] [Semiring R] : Basis ι R R :=
  ofRepr
    { toFun := fun x => Finsupp.single default x
      invFun := fun f => f default
      left_inv := fun x => by simp
      right_inv := fun f => Finsupp.unique_ext (by simp)
      map_add' := fun x y => by simp
      map_smul' := fun c x => by simp }

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `singleton_apply` / 定理 `singleton_apply`

English:
theorem singleton_apply
  given: (ι R : Type*) [Unique ι] [Semiring R] (i)
  statement: Basis.singleton ι R i = 1
  proof: apply_eq_iff.mpr (by simp [Basis.singleton])

中文:
定理 singleton_apply
  条件: (ι R : 类型) [Unique ι] [Semiring R] (i)
  结论: Basis.singleton ι R i = 1
  证明: apply_eq_iff.mpr (by simp [Basis.singleton])

Depends on / 依赖: Basis.singleton, apply_eq_iff, apply_eq_iff.mpr, singleton
-/
theorem singleton_apply (ι R : Type*) [Unique ι] [Semiring R] (i) : Basis.singleton ι R i = 1 :=
  apply_eq_iff.mpr (by simp [Basis.singleton])

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `singleton_repr` / 定理 `singleton_repr`

English:
theorem singleton_repr
  given: (ι R : Type*) [Unique ι] [Semiring R] (x i)
  proof: by simp [Basis.singleton, Unique.eq_default i]

@[simp]

中文:
定理 singleton_repr
  条件: (ι R : 类型) [Unique ι] [Semiring R] (x i)
  证明: by simp [Basis.singleton, Unique.eq_default i]

@[simp]

Depends on / 依赖: Basis.singleton, Unique, Unique.eq_default, eq_default, singleton
-/
theorem singleton_repr (ι R : Type*) [Unique ι] [Semiring R] (x i) :
    (Basis.singleton ι R).repr x i = x := by simp [Basis.singleton, Unique.eq_default i]

@[simp]
/--
theorem `coe_singleton` / 定理 `coe_singleton`

English:
theorem coe_singleton
  given: {ι R : Type*} [Unique ι] [Semiring R]
  proof: by
  ext; simp

中文:
定理 coe_singleton
  条件: {ι R : 类型} [Unique ι] [Semiring R]
  证明: by
  ext; simp
-/
theorem coe_singleton {ι R : Type*} [Unique ι] [Semiring R] :
    ⇑(Basis.singleton ι R) = 1 := by
  ext; simp

end Singleton

section Empty

variable (M)

/--
Definition of `empty` / `empty` 的定义

English:
definition empty
  signature: [Subsingleton M] [IsEmpty ι]
  body: ofRepr 0

中文:
定义 empty
  签名: [Subsingleton M] [IsEmpty ι]
  定义体: ofRepr 0
-/
protected def empty [Subsingleton M] [IsEmpty ι] : Basis ι R M :=
  ofRepr 0

/--
Instance `emptyUnique` / 实例 `emptyUnique`

English:
instance emptyUnique
  signature: [Subsingleton M] [IsEmpty ι]
  body: Basis.empty M
uniq := fun _ => congr_arg ofRepr Subsingleton.elim _ _

中文:
实例 emptyUnique
  签名: [Subsingleton M] [IsEmpty ι]
  定义体: Basis.empty M
uniq := fun _ => congr_arg ofRepr Subsingleton.elim _ _

Depends on / 依赖: Basis.empty
-/
instance emptyUnique [Subsingleton M] [IsEmpty ι] : Unique (Basis ι R M) where
  default := Basis.empty M
uniq := fun _ => congr_arg ofRepr Subsingleton.elim _ _

end Empty

section Module.IsTorsionFree

set_option backward.isDefEq.respectTransparency false in
-- Can't be an instance because the basis can't be inferred.
/--
lemma `isTorsionFree` / 引理 `isTorsionFree`

English:
lemma isTorsionFree
  given: (b : Basis ι R M)
  proof: b.repr.injective.moduleIsTorsionFree _ (by simp)

中文:
引理 isTorsionFree
  条件: (b : Basis ι R M)
  证明: b.repr.injective.moduleIsTorsionFree _ (by simp)
-/
protected lemma isTorsionFree (b : Basis ι R M) :
    Module.IsTorsionFree R M := b.repr.injective.moduleIsTorsionFree _ (by simp)

/--
theorem `smul_eq_zero` / 定理 `smul_eq_zero`

English:
theorem smul_eq_zero
  given: [IsDomain R] (b : Basis ι R M) {c : R} {x : M}
  proof: by have := b.isTorsionFree; exact smul_eq_zero

中文:
定理 smul_eq_zero
  条件: [IsDomain R] (b : Basis ι R M) {c : R} {x : M}
  证明: by have := b.isTorsionFree; exact smul_eq_zero
-/
protected theorem smul_eq_zero [IsDomain R] (b : Basis ι R M) {c : R} {x : M} :
    c • x = 0 ↔ c = 0 ∨ x = 0 := by have := b.isTorsionFree; exact smul_eq_zero

end Module.IsTorsionFree

section Singleton

/--
theorem `basis_singleton_iff` / 定理 `basis_singleton_iff`

English:
theorem basis_singleton_iff
  statement: {R M : Type*} [Ring R] [IsDomain R] [AddCommGroup M] [Module R M]
  proof: by
  constructor
  · rintro ⟨b⟩
    refine ⟨b default, b.linearIndependent.ne_zero _, ?_⟩
    simpa [span_singleton_eq_top_iff, Set.range_unique] using b.span_eq
  · rintro ⟨x, nz, w⟩
refine ⟨ofRepr LinearEquiv.symm
      { toFun := fun f => f default • x
        invFun := fun y => Finsupp.single de

中文:
定理 basis_singleton_iff
  结论: {R M : 类型} [Ring R] [IsDomain R] [AddCommGroup M] [Module R M]
  证明: by
  constructor
  · rintro ⟨b⟩
    refine ⟨b default, b.linearIndependent.ne_zero _, ?_⟩
    simpa [span_singleton_eq_top_iff, Set.range_unique] using b.span_eq
  · rintro ⟨x, nz, w⟩
refine ⟨ofRepr LinearEquiv.symm
      { toFun := fun f => f default • x
        invFun := fun y => Finsupp.single de

Depends on / 依赖: Finsupp, Finsupp.add_apply, Finsupp.coe_smul, Finsupp.single, Finsupp.unique_ext, LinearEquiv, LinearEquiv.symm, Pi.smul_apply, Set.range_unique, add_apply, add_smul, b.linearIndependent.ne_zero, b.span_eq, coe_smul, invFun, left_inv, linearIndependent, map_add, map_smul, ne_zero
-/
theorem basis_singleton_iff {R M : Type*} [Ring R] [IsDomain R] [AddCommGroup M] [Module R M]
    [IsTorsionFree R M] (ι : Type*) [Unique ι] :
    Nonempty (Basis ι R M) ↔ exists x != 0, forall y : M, exists r : R, r • x = y := by
  constructor
  · rintro ⟨b⟩
    refine ⟨b default, b.linearIndependent.ne_zero _, ?_⟩
    simpa [span_singleton_eq_top_iff, Set.range_unique] using b.span_eq
  · rintro ⟨x, nz, w⟩
refine ⟨ofRepr LinearEquiv.symm
      { toFun := fun f => f default • x
        invFun := fun y => Finsupp.single default (w y).choose
        left_inv := fun f => Finsupp.unique_ext ?_
        right_inv := fun y => ?_
        map_add' := fun y z => ?_
        map_smul' := fun c y => ?_ }⟩
    · simp [Finsupp.add_apply, add_smul]
    · simp only [Finsupp.coe_smul, Pi.smul_apply, RingHom.id_apply]
      rw [← smul_assoc]
    · refine smul_left_injective _ nz ?_
      simp only [Finsupp.single_eq_same]
      exact (w (f default • x)).choose_spec
    · simp only [Finsupp.single_eq_same]
      exact (w y).choose_spec

end Singleton
end Basis

open Fintype in
/--
lemma `card_fintype` / 引理 `card_fintype`

English:
lemma card_fintype
  statement: [Semiring R] [AddCommMonoid M] [Module R M] [Fintype ι] (b : Basis ι R M)
  proof: by
  classical
    calc
      card M = card (ι -> R) := card_congr b.equivFun.toEquiv
      _ = card R ^ card ι := by simp

中文:
引理 card_fintype
  结论: [Semiring R] [AddCommMonoid M] [Module R M] [Fintype ι] (b : Basis ι R M)
  证明: by
  classical
    calc
      card M = card (ι -> R) := card_congr b.equivFun.toEquiv
      _ = card R ^ card ι := by simp

Depends on / 依赖: b.equivFun.toEquiv, card_congr, classical, equivFun, toEquiv
-/
lemma card_fintype [Semiring R] [AddCommMonoid M] [Module R M] [Fintype ι] (b : Basis ι R M)
    [Fintype R] [Fintype M] :
    card M = card R ^ card ι := by
  classical
    calc
      card M = card (ι -> R) := card_congr b.equivFun.toEquiv
      _ = card R ^ card ι := by simp

end Module
