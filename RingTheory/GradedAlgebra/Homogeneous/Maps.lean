/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.GradedAlgebra.RingHom

/-!
# Maps on homogeneous ideals

In this file we define `HomogeneousIdeal.map` and `HomogeneousIdeal.comap`.
-/

@[expose] public section

namespace HomogeneousIdeal

section arbitrary_grading

variable {A B C σ τ ω ι F G : Type*}
  [Semiring A] [Semiring B] [Semiring C]
  [SetLike σ A] [SetLike τ B] [SetLike ω C]
  [AddSubmonoidClass σ A] [AddSubmonoidClass τ B] [AddSubmonoidClass ω C]
  [DecidableEq ι] [AddMonoid ι]
  {𝒜 : ι -> σ} {ℬ : ι -> τ} {𝒞 : ι -> ω}
  [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]
  (f : 𝒜 ->+*ᵍ ℬ) (g : ℬ ->+*ᵍ 𝒞)

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (I : HomogeneousIdeal 𝒜)
  body: I.toIdeal.map f
  is_homogeneous' i b hb := by
    rw [Ideal.map] at hb
    induction hb using Submodule.span_induction generalizing i with
    | zero => simp
    | add => simp [*, Ideal.add_mem]
    | mem a ha =>
      obtain ⟨a, ha, rfl⟩ := ha
      rw [← f.map_directSumDecompose]
      exact Ideal.mem_map_of_mem _ (I.2 _ ha)
    | smul a₁ a₂ ha₂ ih =>
      classical rw [smul_eq_mul, DirectSum.decompose_mul, DirectSum.coe_mul_apply]
exact sum_mem fun ij hij => Ideal.mul_mem_left _ _ ih _

中文:
定义 map
  签名: (I : HomogeneousIdeal 𝒜)
  定义体: I.toIdeal.map f
  is_homogeneous' i b hb := by
    rw [Ideal.map] at hb
    induction hb using Submodule.span_induction generalizing i with
    | zero => simp
    | add => simp [*, Ideal.add_mem]
    | mem a ha =>
      obtain ⟨a, ha, rfl⟩ := ha
      rw [← f.map_directSumDecompose]
      exact Ideal.mem_map_of_mem _ (I.2 _ ha)
    | smul a₁ a₂ ha₂ ih =>
      classical rw [smul_eq_mul, DirectSum.decompose_mul, DirectSum.coe_mul_apply]
exact sum_mem fun ij hij => Ideal.mul_mem_left _ _ ih _

Depends on / 依赖: I.toIdeal.map, toIdeal
-/
def map (I : HomogeneousIdeal 𝒜) : HomogeneousIdeal ℬ where
  __ := I.toIdeal.map f
  is_homogeneous' i b hb := by
    rw [Ideal.map] at hb
    induction hb using Submodule.span_induction generalizing i with
    | zero => simp
    | add => simp [*, Ideal.add_mem]
    | mem a ha =>
      obtain ⟨a, ha, rfl⟩ := ha
      rw [← f.map_directSumDecompose]
      exact Ideal.mem_map_of_mem _ (I.2 _ ha)
    | smul a₁ a₂ ha₂ ih =>
      classical rw [smul_eq_mul, DirectSum.decompose_mul, DirectSum.coe_mul_apply]
exact sum_mem fun ij hij => Ideal.mul_mem_left _ _ ih _

/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (I : HomogeneousIdeal ℬ)
  body: I.toIdeal.comap f
  is_homogeneous' n a ha := by
    rw [Ideal.mem_comap]; rw [HomogeneousIdeal.mem_iff]; rw [f.map_directSumDecompose]
    exact I.2 _ ha

中文:
定义 comap
  签名: (I : HomogeneousIdeal ℬ)
  定义体: I.toIdeal.comap f
  is_homogeneous' n a ha := by
    rw [Ideal.mem_comap]; rw [HomogeneousIdeal.mem_iff]; rw [f.map_directSumDecompose]
    exact I.2 _ ha

Depends on / 依赖: I.toIdeal.comap, toIdeal
-/
def comap (I : HomogeneousIdeal ℬ) : HomogeneousIdeal 𝒜 where
  __ := I.toIdeal.comap f
  is_homogeneous' n a ha := by
    rw [Ideal.mem_comap]; rw [HomogeneousIdeal.mem_iff]; rw [f.map_directSumDecompose]
    exact I.2 _ ha

variable {I I₁ I₂ I₃ : HomogeneousIdeal 𝒜} {J J₁ J₂ J₃ : HomogeneousIdeal ℬ}
  {K : HomogeneousIdeal 𝒞}

/--
lemma `map_le_iff_le_comap` / 引理 `map_le_iff_le_comap`

English:
lemma map_le_iff_le_comap
  statement: I.map f <= J ↔ I <= J.comap f
  proof: Ideal.map_le_iff_le_comap

alias ⟨le_comap_of_map_le, map_le_of_le_comap⟩ := map_le_iff_le_comap

中文:
引理 map_le_iff_le_comap
  结论: I.map f <= J ↔ I <= J.comap f
  证明: Ideal.map_le_iff_le_comap

alias ⟨le_comap_of_map_le, map_le_of_le_comap⟩ := map_le_iff_le_comap

Depends on / 依赖: Ideal.map_le_iff_le_comap, map_le_iff_le_comap
-/
lemma map_le_iff_le_comap : I.map f <= J ↔ I <= J.comap f := Ideal.map_le_iff_le_comap

alias ⟨le_comap_of_map_le, map_le_of_le_comap⟩ := map_le_iff_le_comap

/--
theorem `gc_map_comap` / 定理 `gc_map_comap`

English:
theorem gc_map_comap
  statement: GaloisConnection (map f) (comap f)
  proof: fun _ _ =>
  map_le_iff_le_comap f

中文:
定理 gc_map_comap
  结论: GaloisConnection (map f) (comap f)
  证明: fun _ _ =>
  map_le_iff_le_comap f
-/
theorem gc_map_comap : GaloisConnection (map f) (comap f) := fun _ _ =>
  map_le_iff_le_comap f

/--
lemma `map_mono` / 引理 `map_mono`

English:
lemma map_mono
  statement: Monotone (map f)
  proof: (gc_map_comap f).monotone_l

中文:
引理 map_mono
  结论: 递增 (map f)
  证明: (gc_map_comap f).monotone_l
-/
@[mono, aesop safe apply] lemma map_mono : Monotone (map f) := (gc_map_comap f).monotone_l

/--
lemma `comap_mono` / 引理 `comap_mono`

English:
lemma comap_mono
  statement: Monotone (comap f)
  proof: (gc_map_comap f).monotone_u

中文:
引理 comap_mono
  结论: 递增 (comap f)
  证明: (gc_map_comap f).monotone_u
-/
@[gcongr, mono] lemma comap_mono : Monotone (comap f) := (gc_map_comap f).monotone_u

/--
lemma `toIdeal_comap` / 引理 `toIdeal_comap`

English:
lemma toIdeal_comap
  statement: (J.comap f).toIdeal = J.toIdeal.comap f
  proof: rfl

中文:
引理 toIdeal_comap
  结论: (J.comap f).toIdeal = J.toIdeal.comap f
  证明: rfl
-/
@[simp] lemma toIdeal_comap : (J.comap f).toIdeal = J.toIdeal.comap f := rfl

/--
lemma `coe_comap` / 引理 `coe_comap`

English:
lemma coe_comap
  statement: J.comap f = f ⁻¹' J
  proof: rfl

中文:
引理 coe_comap
  结论: J.comap f = f ⁻¹' J
  证明: rfl
-/
@[simp] lemma coe_comap : J.comap f = f ⁻¹' J := rfl

/--
lemma `toIdeal_map` / 引理 `toIdeal_map`

English:
lemma toIdeal_map
  statement: (I.map f).toIdeal = I.toIdeal.map f
  proof: rfl

中文:
引理 toIdeal_map
  结论: (I.map f).toIdeal = I.toIdeal.map f
  证明: rfl
-/
@[simp] lemma toIdeal_map : (I.map f).toIdeal = I.toIdeal.map f := rfl

/--
Instance `isPrime_comap` / 实例 `isPrime_comap`

English:
instance isPrime_comap
  signature: [J.toIdeal.IsPrime]
  body: inferInstanceAs (J.toIdeal.comap f).IsPrime -- this shows that the simpNF already has the instance

中文:
实例 isPrime_comap
  签名: [J.toIdeal.是素]
  定义体: inferInstanceAs (J.toIdeal.comap f).IsPrime -- this shows that the simpNF already has the instance

Depends on / 依赖: IsPrime, J.toIdeal.comap, already, instance, simpNF, toIdeal
-/
instance isPrime_comap [J.toIdeal.IsPrime] : (J.comap f).toIdeal.IsPrime :=
  inferInstanceAs (J.toIdeal.comap f).IsPrime -- this shows that the simpNF already has the instance

/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  statement: I.map (GradedRingHom.id 𝒜) = I
  proof: ext Ideal.map_id _

中文:
引理 map_id
  结论: I.map (分次环态射.id 𝒜) = I
  证明: ext Ideal.map_id _
-/
@[simp] lemma map_id : I.map (GradedRingHom.id 𝒜) = I := ext Ideal.map_id _

/--
lemma `map_map` / 引理 `map_map`

English:
lemma map_map
  statement: (I.map f).map g = I.map (g.comp f)
  proof: ext Ideal.map_map _ _

中文:
引理 map_map
  结论: (I.map f).map g = I.map (g.comp f)
  证明: ext Ideal.map_map _ _

Depends on / 依赖: Ideal.map_map, map_map
-/
lemma map_map : (I.map f).map g = I.map (g.comp f) := ext Ideal.map_map _ _

/--
lemma `map_comp` / 引理 `map_comp`

English:
lemma map_comp
  statement: I.map (g.comp f) = (I.map f).map g
  proof: (map_map f g).symm

中文:
引理 map_comp
  结论: I.map (g.comp f) = (I.map f).map g
  证明: (map_map f g).symm

Depends on / 依赖: map_map
-/
lemma map_comp : I.map (g.comp f) = (I.map f).map g := (map_map f g).symm

/--
lemma `comap_id` / 引理 `comap_id`

English:
lemma comap_id
  statement: I.comap (GradedRingHom.id 𝒜) = I
  proof: rfl

中文:
引理 comap_id
  结论: I.comap (分次环态射.id 𝒜) = I
  证明: rfl
-/
@[simp] lemma comap_id : I.comap (GradedRingHom.id 𝒜) = I := rfl

/--
lemma `comap_comap` / 引理 `comap_comap`

English:
lemma comap_comap
  statement: (K.comap g).comap f = K.comap (g.comp f)
  proof: rfl

中文:
引理 comap_comap
  结论: (K.comap g).comap f = K.comap (g.comp f)
  证明: rfl
-/
lemma comap_comap : (K.comap g).comap f = K.comap (g.comp f) := rfl

end arbitrary_grading

section canonical_grading

variable {A B C σ τ ω ι F G : Type*}
  [Semiring A] [Semiring B] [Semiring C]
  [SetLike σ A] [SetLike τ B] [SetLike ω C]
  [AddSubmonoidClass σ A] [AddSubmonoidClass τ B] [AddSubmonoidClass ω C]
  [DecidableEq ι] [AddCommMonoid ι] [PartialOrder ι] [CanonicallyOrderedAdd ι]
  {𝒜 : ι -> σ} {ℬ : ι -> τ} {𝒞 : ι -> ω}
  [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]
  {f : 𝒜 ->+*ᵍ ℬ} {g : ℬ ->+*ᵍ 𝒞}

/--
theorem `irrelevant_le_map_comp` / 定理 `irrelevant_le_map_comp`

English:
theorem irrelevant_le_map_comp
  proof: by
  rw [map_comp]
exact hg.trans map_mono _ hf

中文:
定理 irrelevant_le_map_comp
  证明: by
  rw [map_comp]
exact hg.trans map_mono _ hf

Depends on / 依赖: hg.trans, map_comp, map_mono
-/
theorem irrelevant_le_map_comp
    (hf : ℬ₊ <= 𝒜₊.map f) (hg : 𝒞₊ <= ℬ₊.map g) : 𝒞₊ <= 𝒜₊.map (g.comp f) := by
  rw [map_comp]
exact hg.trans map_mono _ hf

end canonical_grading

end HomogeneousIdeal
